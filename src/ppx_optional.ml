open Base
open Ppxlib
open Ast_builder.Default

(* The scope in which to find [Optional_syntax]. [From_module] means using
   module.Optional_syntax.Optional_syntax *)
type module_scope =
  | Use_optional_syntax
  | Use_optional_syntax_optional_syntax
  | From_module of longident loc

module Matched_expression_element = struct
  type t =
    { module_ : module_scope
    ; exp : expression
    }
end

type t =
  { default_module : module_scope
  ; original_matched_expr : expression
  ; elements : Matched_expression_element.t list
  ; match_loc : Location.t
  ; cases : case list
  }

let module_scope_of_option = function
  | None -> Use_optional_syntax
  | Some module_ -> From_module module_
;;

let infer_module_from_core_type ~module_ (core_type : core_type) =
  let default = module_scope_of_option module_ in
  match core_type.ptyp_desc with
  | Ptyp_constr (longident, _params) ->
    (match longident.txt with
     | Lident _ -> Use_optional_syntax_optional_syntax
     | Ldot (longident, _label) ->
       From_module { txt = longident; loc = core_type.ptyp_loc }
     | Lapply _ -> default)
  | _ -> default
;;

let expand_matched_expr ~(module_ : longident loc option) matched_expr =
  let individual_exprs =
    match Ppxlib_jane.Jane_syntax.Expression.of_ast matched_expr with
    | Some (Jexp_tuple _fields, _attrs) ->
      Location.raise_errorf
        ~loc:matched_expr.pexp_loc
        "labeled tuples are unsupported in [%%optional ]"
    | None | Some _ ->
      (match matched_expr.pexp_desc with
       | Pexp_tuple exprs -> exprs
       | _ -> [ matched_expr ])
  in
  List.map individual_exprs ~f:(fun exp ->
    match
      Ppxlib_jane.Shim.Expression_desc.of_parsetree ~loc:exp.pexp_loc exp.pexp_desc
    with
    | Pexp_constraint (_exp, Some core_type, _) ->
      { Matched_expression_element.module_ =
          infer_module_from_core_type ~module_ core_type
      ; exp
      }
    | _ -> { module_ = module_scope_of_option module_; exp })
;;

let optional_syntax_str = "Optional_syntax"

let optional_syntax ~module_ : Longident.t =
  match (module_ : module_scope) with
  | Use_optional_syntax -> Lident optional_syntax_str
  | Use_optional_syntax_optional_syntax ->
    Ldot (Lident optional_syntax_str, optional_syntax_str)
  | From_module id -> Ldot (Ldot (id.txt, optional_syntax_str), optional_syntax_str)
;;

let eoperator ~loc ~module_ func =
  let lid : Longident.t = Ldot (optional_syntax ~module_, func) in
  pexp_ident ~loc (Located.mk ~loc lid)
;;

let eunsafe_value = eoperator "unsafe_value"
let eis_none = eoperator "is_none"

let rec assert_binder pat =
  match Ppxlib_jane.Shim.Pattern_desc.of_parsetree pat.ppat_desc with
  | Ppat_alias (pat, _) | Ppat_constraint (pat, _, _) ->
    (* Allow "Some (_ as x)" and "Some (_ : typ)" *)
    assert_binder pat
  | Ppat_var _ | Ppat_any -> ()
  | _ ->
    Location.raise_errorf
      ~loc:pat.ppat_loc
      "sub patterns are restricted to variable names, wildcards and aliases"
;;

let change_warnings warnings_string e =
  let attr =
    let loc = Location.none in
    attribute
      ~loc
      ~name:{ Location.loc; txt = "ocaml.warning" }
      ~payload:(PStr [ pstr_eval ~loc (estring ~loc warnings_string) [] ])
  in
  { e with pexp_attributes = attr :: e.pexp_attributes }
;;

let disable_all_warnings e = change_warnings "-a" e
let hide_expr e = e |> disable_all_warnings |> Merlin_helpers.hide_expression
let disable_unused_var_warning e = change_warnings "-unused-var" e
let varname i = Printf.sprintf "__ppx_optional_e_%i" i
let evar ~loc i = evar ~loc (varname i)
let pvar ~loc i = pvar ~loc (varname i)

let get_pattern_and_bindings ~loc ~module_ i pattern =
  let rec loop pat bindings =
    let option_binding x =
      value_binding ~loc ~pat:(ppat_var ~loc x) ~expr:(evar ~loc i)
    in
    let unsafe_value_binding x =
      value_binding
        ~loc
        ~pat:[%pat? ([%p x] : _)]
        ~expr:(eapply ~loc (eunsafe_value ~loc ~module_) [ evar ~loc i ])
    in
    match pat with
    | { ppat_desc = Ppat_alias (pat, x); _ } ->
      let binding = option_binding x in
      loop pat (binding :: bindings)
    | { ppat_desc = Ppat_var x; _ } ->
      let binding = option_binding x in
      [%pat? _], binding :: bindings
    | [%pat? Some [%p? x]] ->
      assert_binder x;
      let binding = unsafe_value_binding x in
      [%pat? false], binding :: bindings
    | [%pat? None] -> [%pat? true], bindings
    | [%pat? _] -> pat, bindings
    | [%pat? [%p? l] | [%p? r]] ->
      (* At this scope, we're considering a single optional value, so all option bindings
         must be the same option, and all value bindings must be the same value. The fake
         match will cause the compiler to complain if both sides of the pattern do not
         bind the same values, or bind them with different types. So we can safely ignore
         one set of bindings here, as we know the other set must be equivalent. *)
      let l, bindings = loop l bindings
      and r, (_ : value_binding list) = loop r bindings in
      (* N.b. this could be [%pat? [%p l] | [%p r]] but it breaks ocamlformat. *)
      { pat with ppat_desc = Ppat_or (l, r) }, bindings
    | _ ->
      Location.raise_errorf
        ~loc:pat.ppat_loc
        "only variable names, None, Some, _ and aliases are supported in [%%optional ]"
  in
  let { ppat_desc; _ }, bindings = loop pattern [] in
  { pattern with ppat_desc; ppat_loc = loc }, bindings
;;

let ignore_pattern binding =
  { binding with pvb_pat = Merlin_helpers.hide_pattern binding.pvb_pat }
;;

let rec rewrite_case
  ~loc
  ~modules_array
  ~default_module
  ~unboxed (* true <=> we're in a [%optional_u] *)
  { pc_lhs = pat; pc_rhs = body; pc_guard }
  =
  let get_module i =
    (* Sadly, we need to be able to handle the case when the length of the matched
       expression doesn't equal the length of the case, in order to produce useful
       error messages (with the proper types). *)
    if i < Array.length modules_array then modules_array.(i) else default_module
  in
  let single_pattern ~ppat_desc ~bindings =
    (* Merlin_helpers.hide_pattern: this overlaps with the pattern used
       in the LHS of the bindings, but we don't want an error. Yet we also
       don't want this to be a ghost location, because if the pattern is
       ill-typed (e.g. too many patterns), we want the location to point
       to the pattern. We hide this pattern, not the LHS of let-bindings, so
       that merlin's go-to-definition works. *)
    let pc_lhs = Merlin_helpers.hide_pattern { pat with ppat_desc } in
    let pc_rhs, pc_guard =
      match bindings with
      | [] -> body, pc_guard
      | _ :: _ ->
        (* The bindings need to be in scope both in the guard and in the body. So we must
           bind the bindings in both. But we must be careful, because a variable might be
           used only in the guard or in the body, and we don't want spurious unused-var
           warnings. We thus copy the guard into the body (to create one scope where all the
           variable are used) and then ignore any unused-var warnings in the guard. *)
        (match pc_guard with
         | None -> pexp_let ~loc Nonrecursive bindings body, None
         | Some guard_exp ->
           let guard_occ =
             Merlin_helpers.hide_expression
               [%expr
                 ignore ([%e guard_exp] : _);
                 assert false]
           in
           let body_with_guard_occurrences =
             [%expr if false then [%e guard_occ] else [%e body]]
           in
           ( pexp_let ~loc Nonrecursive bindings body_with_guard_occurrences
           , Some
               (disable_unused_var_warning
                  (pexp_let
                     ~loc
                     Nonrecursive
                     (List.map ~f:ignore_pattern bindings)
                     guard_exp)) ))
      (* ignore_pattern: we don't want merlin to see both the bindings in the guard and
           in the case body *)
    in
    [ { pc_lhs; pc_rhs; pc_guard } ]
  in
  match Ppxlib_jane.Jane_syntax.Pattern.of_ast pat with
  | Some (Jpat_tuple _fields, _attrs) ->
    Location.raise_errorf
      ~loc:pat.ppat_loc
      "labeled tuples are unsupported in [%%optional ]"
  | None | Some _ ->
    (match pat.ppat_desc with
     | (Ppat_alias (_, x) | Ppat_var x) when Array.length modules_array > 1 ->
       Location.raise_errorf
         ~loc:pat.ppat_loc
         "this pattern would bind a tuple to the variable %s, which is unsupported in \
          [%%optional ]"
         x.txt
     | Ppat_or (pat1, pat2) ->
       (* Just turn disjunctions into a list of individual cases with identical rhs
          expressions and guards. The OCaml manual explicitly says they are evaluated and
          bound left-to-right: https://v2.ocaml.org/manual/patterns.html#sss:pat-or

          If the rhs expression is a lot of code, this could potentially blow up binary size,
          slow down compilation, and/or hurt performance due to cache locality. But we didn't
          support or-patterns for a long time, so most code already just duplicates the rhs,
          and this is much easier than generating an actual or-pattern with correct bindings.
          We can implement that instead if the need arises in the future.

          If there is a [when]-guard, it is possible for it to be evaluated more times than
          it would be in the equivalent (i.e. "fake", not-ppxified) match statement; see the
          "side-effecting guards" test in ../test/ppx_optional_test.ml for more.  *)
       if unboxed
       then
         Location.raise_errorf
           ~loc:pat.ppat_loc
           "or-patterns are not supported with [%%optional_u ].";
       rewrite_case
         ~loc
         ~modules_array
         ~default_module
         ~unboxed
         { pc_lhs = pat1; pc_rhs = body; pc_guard }
       @ rewrite_case
           ~loc
           ~modules_array
           ~default_module
           ~unboxed
           { pc_lhs = pat2; pc_rhs = body; pc_guard }
     | Ppat_tuple patts ->
       let patts, bindings =
         List.mapi patts ~f:(fun i patt ->
           let module_ = get_module i in
           get_pattern_and_bindings ~loc ~module_ i patt)
         |> List.unzip
       in
       single_pattern ~ppat_desc:(Ppat_tuple patts) ~bindings:(List.concat bindings)
     | _ ->
       let pat, bindings =
         get_pattern_and_bindings ~loc 0 pat ~module_:modules_array.(0)
       in
       single_pattern ~ppat_desc:pat.ppat_desc ~bindings)
;;

(** Take the matched expression and replace all its components by a variable, which will
    have been bound previously, wrapped by [wrapper].
    We do keep the location of the initial component for the new one. *)
let rewrite_matched_expr t ~wrapper =
  let subst_and_wrap i { Matched_expression_element.module_; exp } =
    let loc = { exp.pexp_loc with loc_ghost = true } in
    wrapper ~module_ i (evar ~loc i)
  in
  let pexp_desc =
    match t.elements with
    | [ singleton ] -> (subst_and_wrap 0 singleton).pexp_desc
    | list -> Pexp_tuple (List.mapi list ~f:subst_and_wrap)
  in
  let pexp_loc = { t.original_matched_expr.pexp_loc with loc_ghost = true } in
  { pexp_desc; pexp_loc; pexp_loc_stack = []; pexp_attributes = [] }
;;

(* unboxed: true <=> we're in an [optional_u] *)
let real_match ~loc ~unboxed t =
  let new_matched_expr =
    rewrite_matched_expr t ~wrapper:(fun ~module_ (_ : int) expr ->
      eapply ~loc (eis_none ~loc ~module_) [ expr ])
  in
  let modules = List.map t.elements ~f:(fun { module_; _ } -> module_) in
  let cases =
    List.concat_map
      t.cases
      ~f:
        (rewrite_case
           ~loc
           ~modules_array:(Array.of_list modules)
           ~default_module:t.default_module
           ~unboxed)
  in
  pexp_match ~loc new_matched_expr cases
;;

(* Represents the structure of or-patterns. *)
module Disjunction_tree = struct
  type 'a t =
    | Leaf of
        { pattern : pattern
        ; a : 'a
        }
    | Node of
        { pattern : pattern
        ; l : 'a t
        ; r : 'a t
        }

  let rec iter t ~f =
    match t with
    | Leaf { pattern = _; a } -> f a
    | Node { pattern = _; l; r } ->
      iter l ~f;
      iter r ~f
  ;;

  let rec to_pattern t ~f =
    match t with
    | Leaf { pattern; a } -> f pattern a
    | Node { pattern; l; r } ->
      { pattern with ppat_desc = Ppat_or (to_pattern l ~f, to_pattern r ~f) }
  ;;
end

(* Split a [Some _ as x] pattern into two, [Some _] and [_ as x]. The latter could just be
   [x], but we err on the side of caution and replace a [Ppat_alias _] with another
   [Ppat_alias _] rather than a [Ppat_var _]. Because this is taking the [Ppat_constr _]
   pattern that was nested inside the alias and turning it into a sibling AST node, they
   should be ghosts. However, we take some care to provide reasonable locations for the
   new AST nodes, such that the left-hand pattern extends from the start of the outermost
   alias to the end of the innermost pattern, and the right-hand pattern extends from the
   start of the alias binding (i.e. [x]) to the end of the outermost alias. *)
let split_fake_alias_pattern lhs ((x, _) as alias) aliases =
  (* [ppat_loc_stack] represents relocations of a pattern by the parser, in particular due
     to nested parentheses. [ppat_loc] is the outermost span, and the stack is ordered
     from outer to inner. [ppat_loc] and [ppat_loc_stack] can thus be viewed as a
     nonempty stack. Here we take a list of locations ordered from inner to outer (i.e.
     reversed) and push them down onto an existing nonempty stack. [merge] is used to
     enforce constraints on the boundaries of the left and right patterns (see above). *)
  let relocate_from_inner_to_outer locs loc loc_stack ~merge =
    List.fold locs ~init:(loc, loc_stack) ~f:(fun ((hd, tl) as acc) loc ->
      let loc =
        { loc_start = merge loc.loc_start hd.loc_start
        ; loc_end = merge loc.loc_end hd.loc_end
        ; loc_ghost = loc.loc_ghost
        }
      in
      if Location.compare loc hd = 0 then acc else loc, hd :: tl)
  in
  List.fold
    (alias :: aliases)
    ~init:(lhs, ppat_any ~loc:{ x.loc with loc_ghost = true })
    ~f:(fun (lhs, rhs) (x, pat) ->
      let inner_loc, rev_loc_stack =
        List.fold pat.ppat_loc_stack ~init:(pat.ppat_loc, []) ~f:(fun (hd, tl) loc ->
          loc, hd :: tl)
      in
      let lhs_loc, lhs_loc_stack =
        relocate_from_inner_to_outer
          (inner_loc :: rev_loc_stack)
          lhs.ppat_loc
          lhs.ppat_loc_stack
          ~merge:Location.min_pos
      in
      let rhs_loc, rhs_loc_stack =
        relocate_from_inner_to_outer
          rev_loc_stack
          { inner_loc with loc_start = rhs.ppat_loc.loc_start }
          []
          ~merge:Location.max_pos
      in
      ( { lhs with ppat_loc = lhs_loc; ppat_loc_stack = lhs_loc_stack }
      , { ppat_desc = Ppat_alias (rhs, x)
        ; ppat_loc = rhs_loc
        ; ppat_loc_stack = rhs_loc_stack
        ; ppat_attributes = pat.ppat_attributes
        } ))
;;

(* Take a pattern like [(Some _ | None) as x] and covert it to [Some _ as x | None as x].
   This is pretty similar to the above, but subtly different enough for combining them to
   be more code than it's worth. *)
let invert_fake_or_pattern_and_aliases pat1 pat2 alias aliases =
  let relocate_from_inner_to_outer locs loc ~merge ~override_loc_ghost =
    List.fold locs ~init:(loc, []) ~f:(fun ((hd, tl) as acc) loc ->
      let loc =
        { loc_start = merge loc.loc_start hd.loc_start
        ; loc_end = merge loc.loc_end hd.loc_end
        ; loc_ghost = Option.value override_loc_ghost ~default:loc.loc_ghost
        }
      in
      if Location.compare loc hd = 0 then acc else loc, hd :: tl)
  in
  List.fold (alias :: aliases) ~init:(pat1, pat2) ~f:(fun (pat1, pat2) (x, pat) ->
    let inner_loc, rev_loc_stack =
      List.fold pat.ppat_loc_stack ~init:(pat.ppat_loc, []) ~f:(fun (hd, tl) loc ->
        loc, hd :: tl)
    in
    let pat1_loc, pat1_loc_stack =
      relocate_from_inner_to_outer
        rev_loc_stack
        { inner_loc with loc_end = pat1.ppat_loc.loc_end; loc_ghost = true }
        ~merge:Location.min_pos
        ~override_loc_ghost:(Some true)
    in
    let pat2_loc, pat2_loc_stack =
      relocate_from_inner_to_outer
        rev_loc_stack
        { inner_loc with loc_start = pat2.ppat_loc.loc_start }
        ~merge:Location.max_pos
        ~override_loc_ghost:None
    in
    ( { ppat_desc = Ppat_alias (pat1, x)
      ; ppat_loc = pat1_loc
      ; ppat_loc_stack = pat1_loc_stack
      ; ppat_attributes = pat.ppat_attributes
      }
    , { ppat_desc = Ppat_alias (pat2, x)
      ; ppat_loc = pat2_loc
      ; ppat_loc_stack = pat2_loc_stack
      ; ppat_attributes = pat.ppat_attributes
      } ))
;;

(* A "fake" pattern is one which requires a [Foo.t option] expression to be typed
   correctly, effectively only [Ppat_construct _], but we rely on
   [get_pattern_and_bindings] to complain about other unsupported patterns. A "real"
   pattern is one which requires a [Foo.Option.t] expression. Patterns requiring "both"
   must be matched against a [Foo.t option * Foo.Option.t]. Wildcards can be used with
   "any" of the above. We could always generate "both" patterns but it would come at the
   cost of potentially confusing type errors, so we avoid them where possible. *)
let rec analyze_fake_pattern pattern : _ Disjunction_tree.t =
  match pattern.ppat_desc with
  | Ppat_any -> Leaf { pattern; a = `Any }
  | Ppat_var _ -> Leaf { pattern; a = `Real }
  | Ppat_or (pat1, pat2) ->
    Node { pattern; l = analyze_fake_pattern pat1; r = analyze_fake_pattern pat2 }
  | Ppat_alias (pat, x) ->
    let original_alias_pattern = pattern in
    let rec loop pattern alias aliases : _ Disjunction_tree.t =
      match pattern.ppat_desc with
      | Ppat_any | Ppat_var _ -> Leaf { pattern = original_alias_pattern; a = `Real }
      | Ppat_or (pat1, pat2) ->
        let pat1, pat2 = invert_fake_or_pattern_and_aliases pat1 pat2 alias aliases in
        Node
          { pattern = original_alias_pattern
          ; l = analyze_fake_pattern pat1
          ; r = analyze_fake_pattern pat2
          }
      | Ppat_alias (pat, x) -> loop pat (x, pattern) (alias :: aliases)
      | _ ->
        Leaf
          { pattern = original_alias_pattern
          ; a = `Both (split_fake_alias_pattern pattern alias aliases)
          }
    in
    loop pat (x, pattern) []
  | _ -> Leaf { pattern; a = `Fake }
;;

let rec analyze_fake_patterns pattern : _ Disjunction_tree.t =
  match pattern.ppat_desc with
  | Ppat_or (pat1, pat2) ->
    Node { pattern; l = analyze_fake_patterns pat1; r = analyze_fake_patterns pat2 }
  | Ppat_tuple patts ->
    Leaf { pattern; a = Array.of_list_map ~f:analyze_fake_pattern patts }
  | _ -> Leaf { pattern; a = [| analyze_fake_pattern pattern |] }
;;

let make_fake_pattern_compatible expr_kind patt_tree =
  Disjunction_tree.to_pattern patt_tree ~f:(fun pat patt_kind ->
    match expr_kind, patt_kind with
    | `Fake, `Fake | `Real, `Real | _, `Any -> pat
    | `Both, ((`Fake | `Real | `Both _) as kind) ->
      let wildcard = lazy (ppat_any ~loc:Location.none) in
      let fake, real =
        match kind with
        | `Fake -> pat, force wildcard
        | `Real -> force wildcard, pat
        | `Both both -> both
      in
      ppat_tuple ~loc:{ pat.ppat_loc with loc_ghost = true } [ fake; real ]
    | `Any, (`Fake | `Real | `Both _) | `Fake, (`Real | `Both _) | `Real, (`Fake | `Both _)
      ->
      Location.raise_errorf
        ~loc:pat.ppat_loc
        "Bug in [%%optional ]: this pattern is incompatible with the corresponding fake \
         expression")
;;

let make_fake_patterns_compatible expr_kinds patt_tree =
  Disjunction_tree.to_pattern patt_tree ~f:(fun pat patt_trees ->
    match patt_trees with
    | [| patt_tree |] -> make_fake_pattern_compatible expr_kinds.(0) patt_tree
    | _ ->
      let patts =
        Array.mapi patt_trees ~f:(fun i patt_tree ->
          make_fake_pattern_compatible expr_kinds.(i) patt_tree)
        |> Array.to_list
      in
      { pat with ppat_desc = Ppat_tuple patts })
;;

let translate_fake_match_cases cases ~num_exprs =
  let patt_trees =
    Array.of_list_map cases ~f:(fun { pc_lhs = pat; _ } -> analyze_fake_patterns pat)
  in
  let max_num_patts = ref num_exprs in
  Array.iter patt_trees ~f:(fun patt_tree ->
    Disjunction_tree.iter patt_tree ~f:(fun patt_trees ->
      Ref.replace max_num_patts (max (Array.length patt_trees))));
  let expr_kinds = Array.create ~len:!max_num_patts `Any in
  (* We need to ensure the fake expression can generate bindings for all of its
     corresponding patterns. *)
  Array.iter patt_trees ~f:(fun patt_tree ->
    Disjunction_tree.iter patt_tree ~f:(fun patt_trees ->
      Array.iteri patt_trees ~f:(fun i patt_tree ->
        Disjunction_tree.iter patt_tree ~f:(fun patt_kind ->
          match expr_kinds.(i), patt_kind with
          | `Both, _ | `Fake, `Fake | `Real, `Real | _, `Any -> ()
          | `Any, ((`Fake | `Real) as expr_kind) -> expr_kinds.(i) <- expr_kind
          | `Fake, `Real | `Real, `Fake | _, `Both _ -> expr_kinds.(i) <- `Both))));
  let cases =
    List.mapi cases ~f:(fun c case ->
      { case with pc_lhs = make_fake_patterns_compatible expr_kinds patt_trees.(c) })
  in
  cases, expr_kinds
;;

(* The fake match's aliases have types like [int option] instead of [Int.Option], so we
   match on tuples e.g. [Some (unsafe_value x), x], then rewrite patterns to attach
   aliases and vars to the second element rather than the first. *)
let fake_match t =
  let cases, kinds =
    translate_fake_match_cases t.cases ~num_exprs:(List.length t.elements)
  in
  let new_matched_expr =
    rewrite_matched_expr t ~wrapper:(fun ~module_ i expr ->
      let loc = expr.pexp_loc in
      let fake_option =
        [%expr
          (* This code will never be executed, it is just here so the type checker
              generates nice error messages. *)
          if [%e eis_none ~loc ~module_] [%e expr]
          then None
          else Some ([%e eunsafe_value ~loc ~module_] [%e expr])]
      in
      match kinds.(i) with
      | `Fake -> fake_option
      | `Any | `Real -> expr
      | `Both -> [%expr [%e fake_option], [%e expr]])
  in
  pexp_match ~loc:{ t.match_loc with loc_ghost = true } new_matched_expr cases
;;

let bindings_for_matched_expr matched_expr =
  let bind i expr =
    let loc = { expr.pexp_loc with loc_ghost = true } in
    value_binding ~loc ~pat:(pvar ~loc i) ~expr
  in
  List.mapi matched_expr ~f:(fun i { Matched_expression_element.exp; _ } -> bind i exp)
;;

let expand_match ~unboxed ~match_loc ~(module_ : longident loc option) matched_expr cases =
  let t =
    { default_module = module_scope_of_option module_
    ; original_matched_expr = matched_expr
    ; elements = expand_matched_expr ~module_ matched_expr
    ; match_loc
    ; cases
    }
  in
  let bindings = bindings_for_matched_expr t.elements in
  let loc = { match_loc with loc_ghost = true } in
  let body =
    if unboxed
    then real_match ~loc ~unboxed t
    else (
      let fake_match =
        (* The types in this branch actually match what the user would expect given the source
           code, so we tell merlin to do all its work in here. *)
        Merlin_helpers.focus_expression (fake_match t)
      in
      let real_match =
        (* The types here actually have nothing to do with what's in the source ([bool]
           appears for example), so we hide this branch. This also disables warnings, but
           that's OK because we rely on the other match we generate for error messages. *)
        real_match ~loc ~unboxed t |> hide_expr
      in
      [%expr if false then [%e fake_match] else [%e real_match]])
  in
  pexp_let ~loc Nonrecursive bindings body
;;

(* We add the indirection instead of directly matching on [pexp_match] when declaring the
   extension because we want more informative error messages than "Extension was not
   translated". *)
let expand_match ~unboxed ~loc ~path:_ ~arg:(module_ : longident loc option) e =
  Ast_pattern.parse
    Ast_pattern.(pexp_match __ __)
    loc
    e
    ~on_error:(fun () ->
      Location.raise_errorf ~loc "[%%optional ] must apply to a match statement")
    (expand_match ~unboxed ~match_loc:e.pexp_loc ~module_)
;;

let optional =
  Extension.declare_with_path_arg
    "optional"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (expand_match ~unboxed:false)
;;

let optional_u =
  Extension.declare_with_path_arg
    "optional_u"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (expand_match ~unboxed:true)
;;

let () = Driver.register_transformation "optional" ~extensions:[ optional ]
let () = Driver.register_transformation "optional_u" ~extensions:[ optional_u ]
(* The fake match built above doesn't work for unboxed types. So [optional_u] doesn't
   generate it. *)
