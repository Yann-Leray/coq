(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let check_exists_rewrite_rules sp =
  if Nametab.RewriteRules.exists sp then
    raise (DeclareUniv.AlreadyDeclared (Some "Rewrite Rules", Libnames.basename sp))
  else ()

let qualify_rewrite_rules i dp id =
  i, Libnames.add_path_suffix dp id

let do_rewrite_rules_name ~check i dp (id, rules) =
  let i, sp = qualify_rewrite_rules i dp id in
  if check then check_exists_rewrite_rules sp;
  Nametab.RewriteRules.push i sp rules

let cache_rewrite_rules_names (prefix, decl) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.path_pop_n_suffixes depth prefix.Libobject.obj_path in
  do_rewrite_rules_name ~check:true (Nametab.Until 1) dp decl

let load_rewrite_rules_names i (prefix, decl) =
  do_rewrite_rules_name ~check:false (Nametab.Until i) prefix.Libobject.obj_path decl

let open_rewrite_rules_names i (prefix, decl) =
  do_rewrite_rules_name ~check:false (Nametab.Exactly i) prefix.Libobject.obj_path decl

let discharge_rewrite_rules decl = Some decl

let input_rewrite_rules_names : variable * RewriteRules.t -> Libobject.obj =
  let open Libobject in
  declare_named_object_gen
    { (default_object "Rewrite Rules") with
      cache_function = cache_rewrite_rules_names;
      load_function = load_rewrite_rules_names;
      open_function = filtered_open open_rewrite_rules_names;
      discharge_function = discharge_rewrite_rules;
      classify_function = (fun a -> Escape) }

let inRewriteRules id =
  let rrl = RewriteRules.make (Global.current_dirpath ()) id in
  Lib.add_leaf (input_rewrite_rules_names (id, rrl))
