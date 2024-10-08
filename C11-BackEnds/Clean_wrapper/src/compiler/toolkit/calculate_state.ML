(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature CALCULATE_STATE =
sig

  type var_info = ProgramAnalysis.var_info
  type csenv = ProgramAnalysis.csenv
  type 'a ctype = 'a Absyn.ctype
  type ecenv = Absyn.ecenv
  type 'a rcd_env = 'a ProgramAnalysis.rcd_env
  type nm_info = ProgramAnalysis.nm_info
(*
  val define_enum_consts : ecenv -> theory -> theory
*)
  type staterep
  val globals_all_addressed : bool Config.T
  val populate_globals : bool Config.T
  val record_globinits : bool Config.T
  val current_C_filename : string Config.T

  val ctype_to_typ : theory * int ctype -> typ
  datatype var_sort = Local of string
                    | NSGlobal
                    | AddressedGlobal
                    | UntouchedGlobal

  val create_state : csenv -> staterep

  val mk_thy_types :
      csenv -> bool -> theory ->
      theory *
      (string * (string * typ * int ctype) list) list

  val mk_thy_decls :
      staterep -> {mstate_ty : typ,gstate_ty : typ, owners : string list} ->
      theory ->
      theory *
      (nm_info * typ * int ctype option * var_sort) list *
      (typ,term,thm list)Element.ctxt list *
      (binding * (bool * ProgramAnalysis.nm_info option * (binding * typ * mixfix)) list) *
      (binding * (bool * ProgramAnalysis.nm_info option * (binding * typ * mixfix)) list)
(*
  val gen_umm_types_file : csenv -> string -> unit
*)
  type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table
  val mk_mungedb : (nm_info * typ * int ctype option * var_sort) list ->
                   mungedb


  (* storing csenv's in the theory *)
  val store_csenv : string * csenv -> theory -> theory
  val get_csenv : theory -> Input.source -> csenv option
  val get_csenv' : theory -> string -> csenv option
  (* storing ghost-state types in the theory *)
  val store_ghostty : string * typ -> theory -> theory
  val get_ghostty : theory -> string -> typ option
  (* storing mungedb's in the theory *)
  val store_mungedb : string * mungedb -> theory -> theory
  val get_mungedb : theory -> string -> mungedb option

  val get_globals_data : typ -> typ -> theory -> {acc : term, upd : term,
    fields : (string * typ) list}
  val get_standard_globals : typ -> typ -> theory
    -> {hp: ((term * term) * (term * term)),
        phantom: ((term * term) * (term * term)),
        ghost: ((term * term) * (term * term))}

(*
   The isa_decl type corresponds to a program variable in a form that will be
   easy for Isabelle to process.

      vdecl (nm, ty, vsort)  nm is the name of a variable of type ty,
                             declared in function f if fname is Local
                             f, or a global: UntouchedGlobal if it is never
                             modified or addressed, NSGlobal if its
                             address is not taken, or AddressedGlobal
                             if it is.

   [create_state intinfo vars] returns a sequence of abstract Isabelle
   variable information.

   [mk_thy_decls decls] translates such a series into an operation on
   an Isabelle theory, creating various records ('myvars', 'globals',
   with fields corresponding to the variables

*)

end;


structure CalculateState : CALCULATE_STATE =
struct

open Basics Absyn TermsTypes NameGeneration ProgramAnalysis Feedback

val bnm = Binding.name

val (globals_all_addressed, populate_globals, record_globinits,
     current_C_filename) =
    let
      val (gconfig, gsetup) = Attrib.config_bool (bnm "globals_all_addressed") (K false)
      val (pconfig, psetup) = Attrib.config_bool (bnm "populate_globals") (K false)
      val (rconfig, rsetup) = Attrib.config_bool (bnm "record_globinits") (K false)
      val (Cfile_config, csetup) = Attrib.config_string (bnm "current_C_filename") (K "")
    in
      Context.>>(Context.map_theory gsetup o Context.map_theory psetup o
                 Context.map_theory rsetup o Context.map_theory csetup);
      (gconfig, pconfig, rconfig, Cfile_config)
    end
(*
fun define_enum_consts (CE {enumenv, ...}) thy = let
  fun define1 (nm, (value, tyname_opt)) (acc,lthy) = let
    val rhs_v = IntInfo.numeral2w (Signed Int) value
    val typeinfo = case tyname_opt of NONE => "" | SOME s => " (of type "^s^")"
    val _ = informStr(2, "Defining enumeration constant "^nm^typeinfo^
                         " to have value "^
                         Int.toString value^" (signed int)")
    val nm' = NameGeneration.enum_const_name nm
    val binding = Binding.name nm'
    val ((_, (_, th)), lthy) =
        Local_Theory.define ((binding, NoSyn),
                             ((Thm.def_binding binding, []), rhs_v))
                            lthy
    fun upd th t = th :: t
    val acc = case tyname_opt of
                NONE => acc
              | SOME nm => Symtab.map_default (nm, []) (upd th) acc
  in
    (acc, lthy)
  end
  val sfx = NameGeneration.enum_const_summary_lemma_sfx
  fun group_lemma (tynm, ths) lthy =
      (informStr (2, "Adding "^Int.toString (length ths)^
                     " enum definitions for type "^ tynm);
       #2 (Local_Theory.note ((Binding.name(tynm ^ sfx), []), ths) lthy))
  val lthy = Named_Target.theory_init thy
  val (tythms, lthy) = Symtab.fold define1 enumenv (Symtab.empty, lthy)
  val lthy = Symtab.fold group_lemma tythms lthy
in
  Local_Theory.exit_global lthy
end
*)
datatype isa_type = refty of (isa_type option * int ctype)
                  | recd of (string * int ctype)
                  | array of isa_type * int * int ctype
                  | existing of typ * int ctype
type isa_senv = isa_type rcd_env

datatype var_sort =
         Local of string | NSGlobal | AddressedGlobal | UntouchedGlobal
type isa_var = (nm_info * isa_type * var_sort)
datatype isa_decl = vdecl of nm_info * isa_type * var_sort
type staterep = isa_decl list

fun isa_type_to_cty (refty (_, c)) = c
  | isa_type_to_cty (recd(_, c)) = c
  | isa_type_to_cty (array (_, _, c)) = c
  | isa_type_to_cty (existing(_, c)) = c

fun translate_inttype (ty : int ctype) =
  case ty of
    Signed x => existing (IntInfo.ity2wty (Signed x), ty)
  | Unsigned x => existing (IntInfo.ity2wty (Unsigned x), ty)
  | PlainChar => existing (IntInfo.ity2wty PlainChar, ty)
  | Bool => existing (IntInfo.ity2wty Bool, ty)
  | Ptr Void => refty (NONE, ty)
  | Ptr (Function _) => refty (NONE, ty)
  | Ptr ty0 => refty (SOME (translate_inttype ty0), ty)
  | Array(ty0, SOME sz) => array (translate_inttype ty0, sz, ty)
  | Array(_, NONE) => raise Fail "translate_inttype: incomplete array!"
  | StructTy s => recd (s, ty)
  | EnumTy _ => translate_inttype (Signed Int)
  | Ident _ => raise Fail "Should never happen: translate out typedefs"
  | Void => raise Fail "Values of bare void type illegal"
  | Bitfield _ => raise Fail "Can't cope with bitfields"
  | _ =>
    raise Fail ("translate_type: can't cope with "^tyname ty)

val translate_type = translate_inttype

(* translate_vi creates a list of variables that need to be declared
   in the isabelle environment.  The information provided is the name
   of the variable, the "isa type", the name of the enclosing function
   (can be NONE to represent a global var, and the structure
   environment.

   For struct types, additional type declarations need to be made (the
   Isabelle record types need to be declared).  For pointer types,
   additional global variables need to be declared, these will be of a
   function type from a reference type to the type pointed to by the
   variable, and represent the heap.  This augmentation is done by
   augment_decls below.

 *)
fun translate_vi csenv = let
  val untoucheds = calc_untouched_globals csenv
  fun doit vi = let
  in
    case get_vi_type vi of
      Function _ => NONE
    | ty => let
        val isaty = translate_type ty
        val k = get_mname vi
        val var_sort =
            case get_vi_fname vi of
              SOME s => Local s
            | NONE => let
              in
                if MSymTab.defined (get_addressed csenv) k then
                  AddressedGlobal
                else if MSymTab.defined untoucheds k then
                  UntouchedGlobal
                else
                  NSGlobal
              end
      in
        SOME (get_vi_nm_info csenv vi, isaty, var_sort)
      end
  end
in
  doit
end

fun isa_type_to_typ ctxt (ity : isa_type) = let
  fun m s = let
    val thy = Proof_Context.theory_of ctxt
    val known = (Syntax.parse_typ ctxt s; true) handle ERROR _ => false
    val f = if known then Sign.intern_type thy else Sign.full_name thy o Binding.name
  in
    f s
  end
  fun mk_array_size_ty sz =
    (*if sz = ArchArrayMaxCount.array_max_count
      then*) @{typ "array_max_count_ty"}
      (*else mk_numeral_type sz*)
in
  case ity of
    refty (NONE, _) => mk_ptr_ty unit
  | refty (SOME ity0, _) => mk_ptr_ty (isa_type_to_typ ctxt ity0)
  | recd (s, _) => Type (m s, [])
  | array (ity, sz, _) =>
    Type("Arrays.array", [isa_type_to_typ ctxt ity, mk_array_size_ty sz])
  | existing (ty, _) => ty
end

fun ctype_to_typ (thy,c0ty) =
    isa_type_to_typ (thy2ctxt thy) (translate_inttype c0ty)

fun create_state cse = let
  val trans = translate_vi cse
  fun innerfold (vi, acc) =
      case trans vi of
        NONE => acc
      | SOME v => vdecl v :: acc
  fun outerfold (_,vlist) acc = List.foldl innerfold acc vlist
  val vs = Symtab.fold outerfold (get_vars cse) []
in
  vs
end

fun split_vars thy (lvars, gvars) dlist = let
  val split_vars = split_vars thy
in
  case dlist of
    [] => (List.rev lvars, List.rev gvars)
  | vdecl (s, ty, vsort) :: tail => let
      val tuple = (s, isa_type_to_typ (thy2ctxt thy) ty, SOME (isa_type_to_cty ty), vsort)
    in
      case vsort of
        Local _ => split_vars (tuple :: lvars, gvars) tail
      | _ => split_vars (lvars, tuple :: gvars) tail
    end
end

fun listvars f vns =
    case vns of
        [vn] => f vn
      | vn::rest => f vn ^ ", " ^ listvars f rest
      | [] => "<none>"

fun locale_params owners = let
  fun mk_fix (Free(n,ty)) = (Binding.name n, SOME ty, NoSyn)
    | mk_fix _ = raise Fail "locale_params.mk_fix: should never happen"
  val ownership_fixes =
      map (fn oid => mk_fix(Free(oid, nat))) owners
  val fixes =
      Element.Fixes (mk_fix symbol_table :: ownership_fixes)
in
  [fixes]
end

datatype umm_decl = umm_array of int ctype * int
                  | umm_struct of string * (string * int ctype) list
structure UMMKey =
struct
  type key = umm_decl
  fun ord (umm_array _, umm_struct _) = LESS
    | ord (umm_array p1, umm_array p2) = pair_compare
                                             (ctype_compare Int.compare, Int.compare)
                                             (p1, p2)
    | ord (umm_struct _, umm_array _) = GREATER
    | ord (umm_struct (s1, _), umm_struct (s2, _)) = String.compare (s1,s2)
end
structure UMMTab = Table(UMMKey)
local
  structure UMMFlip = FlipTable(structure Table = UMMTab)
in
val ummflip = UMMFlip.flip
end

(*
 * Perform a topological sort of structures such that "parent" structures
 * appear after "child" structures (where a "parent" has a pointer to or
 * includes a "child" structure).
 *
 * Structures may be mutulally dependent; in this case, the structures will
 * appear in the same list in the output.
 *)
fun get_sorted_structs cse =
let
  val rcds = get_senv cse
  val sorted_structs =
      if null rcds then []
      else let
          val (rcdmap,rcdnames) =
              List.foldl (fn (r as (s,_),(tab,nms)) =>
                             (Symtab.update (s, r) tab, s::nms))
                         (Symtab.empty, [])
                         rcds
          fun rcd_neighbours ((s, flds), acc) = let
            fun struct_refs (cty, acc) =
                case cty of
                  Ptr ty' => struct_refs (ty', acc)
                | StructTy s' => Symtab.cons_list (s,s') acc
                | Array(ty', _) => struct_refs (ty', acc)
                | _ => acc
          in
            List.foldl (fn ((_,ty),acc) => struct_refs (ty,acc)) acc flds
          end
          val inclusion_graph = List.foldl rcd_neighbours Symtab.empty rcds
          val inverse_graph = flip_symtab inclusion_graph
          open Topo_Sort
          val sorted0 = topo_sort {cmp = String.compare,
                                   graph = Symtab.lookup_list inclusion_graph,
                                   converse = Symtab.lookup_list inverse_graph}
                                  rcdnames
        in
          map (map (valOf o Symtab.lookup rcdmap)) sorted0
        end
in
  sorted_structs
end
(*
(*
 * Generate an output file "umm_types.txt" that contains information about
 * structures in the input C file.
 *
 * This is required by certain external tools, such as the bitfield generator.
 *)
fun gen_umm_types_file cse outfile =
let
  val num_ty_string = Word_Lib.dest_binT #> string_of_int

  fun write_one strm (recname, flds) = let
    fun isa_to_string (refty (NONE, _)) = "Ptr Unit"
      | isa_to_string (refty (SOME ty, _)) = "Ptr " ^ isa_to_string ty
      | isa_to_string (recd (s, _)) = s
      | isa_to_string (array (ty, n, _)) = "Array " ^ (isa_to_string ty) ^
                                           " " ^ (Int.toString n)
      | isa_to_string (existing (Type(@{type_name "word"},
                                  [Type (@{type_name "Signed_Words.signed"}, [n])]), _)) =
            "Signed_Word " ^ num_ty_string n
      | isa_to_string (existing (Type(@{type_name "word"},
                                      [n]), _)) = "Word " ^ num_ty_string n
      | isa_to_string _ = error "Unexpected type in isa_to_string"

    fun do_one_fld (fldname, fldty) =
        TextIO.output (strm, "\t" ^ fldname ^ ":" ^
                             isa_to_string (translate_type fldty) ^ "\n")

    val _ = TextIO.output (strm, recname ^ "\n")
    val _ = app do_one_fld flds
  in
    TextIO.output (strm, "\n")
  end

  val sorted_structs = get_sorted_structs cse
  val outstrm = TextIO.openOut outfile
  val _ = app (app (write_one outstrm)) sorted_structs
  val _ = TextIO.closeOut outstrm
in
  ()
end
*)
val outfilnameN = "umm_types.txt"

fun mk_thy_types cse install thy = let
  (* Make the necessary theory declarations to make the C file's types work
     in Isabelle.  There are two phases.

     Phase 0:
       For arrays, declaration of the numCopy types corresponding to
       the sizes of the various arrays.  This can be done before
       anything else happens, as it is not dependent on any other types.

       For structs, the basic declaration of the corresponding record
       type, using the RecursiveRecordPackage.  This is complicated by the
       fact that multiple structs may be mutually recursive.  So you
       have to figure out which ones, and declare them all together.
       This requires a topological sort of the struct declarations.
       This phase is also dependent on array sizes having been
       declared correctly because a struct's field may be an array,
       and this requires that array's size type to be declared
       already.

     Phase1:
       UMM property proofs.  These have to happen in the order of
       declaration from the C file (which is reflected in the "state"
       parameter).

     Also return a list of all the record declarations that were made
     for consumption by later phases of the translation.

  *)
  val rcds = get_senv cse
  val sorted_structs = get_sorted_structs cse

  (*open MemoryModelExtras
  open UserTypeDeclChecking
  val umm_prfstate = initial_state*)
  fun new_rcdinfo (recname,flds) thy = let
    fun fldtys (fldname, cty) = (fldname, ctype_to_typ (thy,cty), cty)
  in
    (recname, map fldtys flds)
  end

  fun rcddecls_phase0 (recflds, thy) = let
        val _ =
            informStr(2, "Not defining isabelle type(s) corresponding to \
                         \struct group:")
        val _ = app (fn (recname,flds) =>
                        informStr (2, "  struct " ^ recname^ ", with fields: " ^
                                      listvars #1 flds))
                    recflds
  in
    (*if install then let
        fun mk_rp_fld thy (fldname,cty) = {fldname = fldname,
                                           fldty = ctype_to_typ (thy,cty)}
        fun mk_rp_recd thy (recname, flds) =
            {record_name = recname, fields = map (mk_rp_fld thy) flds}
        fun mk_ctype_instance (recname, _) thy = let
          val recty = Syntax.read_typ_global thy recname

          (* establish the new type as a c_type, which requires no proof, as
             there are no axioms attached to c_type *)
          val c_type_instance_t =
              Logic.mk_of_class(recty, "CTypesDefs.c_type")
          val c_type_instance_ct = Thm.cterm_of (thy2ctxt thy) c_type_instance_t
          val is_c_type_thm =
              Goal.prove_internal (thy2ctxt thy) [] c_type_instance_ct
                                  (fn _ => Class.intro_classes_tac (thy2ctxt thy) [])
          val thy = Axclass.add_arity is_c_type_thm thy

          val _ =
              informStr (2, "Proved  instance "^
                            Syntax.string_of_typ (thy2ctxt thy) recty^
                            " :: c_type")
        in
          thy
        end
      in
        thy |> RecursiveRecordPackage.define_record_type (map (mk_rp_recd thy) recflds)
            |> Basics.fold mk_ctype_instance recflds
      end
    else*)
      thy
  end

  val thy = List.foldl rcddecls_phase0 thy sorted_structs
(*
  (* Yuck, sorry *)
  val _ = gen_umm_types_file cse outfilnameN
*)
  val arrays = List.filter (fn (_, sz) => sz <> 0)
                           (Binaryset.listItems (get_array_mentions cse))
  val umm_events = let
    val evs = map umm_array arrays @ map umm_struct rcds
  in
    if null evs then []
    else let
        val umm_struct_map =
            List.foldl (fn (r as (s,_),acc) => Symtab.update (s,umm_struct r) acc)
                       Symtab.empty
                       rcds
        val umm_array_set =
            List.foldl (fn (a,acc) => Binaryset.add(acc,umm_array a))
                       (Binaryset.empty UMMKey.ord)
                       arrays
        fun toEv ty =
            case ty of
              Array (ty, SOME sz) => let
                val u = umm_array(ty,sz)
              in
                if Binaryset.member(umm_array_set, u) then SOME u else NONE
              end
          | StructTy s => Symtab.lookup umm_struct_map s
          | _ => NONE
        fun umm_included uev =
            case uev of
              umm_array (ty, _) => [ty]
            | umm_struct(_, flds) => map #2 flds
        val inclusion =
            List.foldl
                (fn (u,acc) => UMMTab.update
                                   (u,List.mapPartial toEv (umm_included u))
                                   acc)
                UMMTab.empty
                evs
        val converse = ummflip inclusion
        val sorted_evs = Topo_Sort.topo_sort {graph = UMMTab.lookup_list inclusion,
                                              converse = UMMTab.lookup_list converse,
                                              cmp = UMMKey.ord}
                                             evs
        val _ = List.all (fn l => length l = 1) sorted_evs orelse
                error "Topological sort of object inclusion includes a loop"
      in
        map hd sorted_evs
      end
  end

  fun rcddecl_phase1 (p as (recname, _ (* flds *)), (thy, st, rcdacc)) = let
    val rcdinfo = new_rcdinfo p thy
    val (st, thy1) =
        (*if install then
          (informStr (2, "Proving UMM properties for struct "^recname);
           struct_type cse {struct_type = rcdinfo, state = st}
                       thy)
        else*) (st, thy)
  in
    (thy1, st, rcdinfo :: rcdacc)
  end

  fun arraytype_phase1 ((cty, n), (thy, st, rcdacc)) = let
      val (st', thy') =
          (*if install then
              array_type cse
                         {element_type = ctype_to_typ(thy,cty), array_size =  n,
                          state = st}
                         thy
          else*)
              (st, thy)
  in
      (thy', st', rcdacc)
  end
  fun phase1 (idecl, acc) =
      case idecl of
        umm_array ai => arraytype_phase1 (ai, acc)
      | umm_struct ri => rcddecl_phase1 (ri, acc)

  val (thy, final_state, rcdinfo0)
    = List.foldl phase1 (thy, (), []) umm_events
  val thy = (*if install then UserTypeDeclChecking.finalise final_state thy
            else*) thy
in
  (thy, List.rev rcdinfo0)
end

fun simple s = {isa_name = MString.mk s, src_name = s, src_return_var = false, src_fname = NONE, alias = false}

fun pretty_recdef thy nm vars =
  informStr (0,
    Pretty.big_list
        ("Defining record: " ^ nm ^ " =")
        (map (fn (nm,ity,_,_) =>
                 Pretty.str (MString.dest (#isa_name nm) ^ " :: " ^
                             Syntax.string_of_typ (thy2ctxt thy) ity))
             vars)
    |> Pretty.string_of);

fun categorise_globals (alladdressed, popglobs) l = let
  fun recurse (acc as (ut, ns, ad)) l =
    case l of
      [] => acc
    | (g as (_, _, _, vsort)) :: rest => let
      in
        if not alladdressed orelse not popglobs then let
            val vsort = if alladdressed then AddressedGlobal else vsort
          in
            case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen"
            | UntouchedGlobal => recurse (g::ut,      ns,    ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns,    ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
          end
        else
          case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen #2"
            | UntouchedGlobal => recurse (g::ut,      ns, g::ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns, g::ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
      end
in
  recurse ([],[],[]) l
end

fun mk_thy_decls state {owners,mstate_ty=pmstate_ty,gstate_ty} thy = let
  val rest = state
  fun declare_vars thy = let
    val (lvars0, gvars) = split_vars thy ([], []) rest
    open NameGeneration
    fun mk_globals_rcd thy = let
      val (_ (* utglobs *), nsglobs, _ (* adglobs *)) =
          (* untouched globals, Norbert Schirmer Globals, addressed globals *)
          categorise_globals (Config.get_global thy globals_all_addressed,
                              Config.get_global thy populate_globals)
                             gvars
      val _ = if not (null gvars) then pretty_recdef thy "globals" nsglobs
              else ()
      val gflds =
          [(false, NONE, (bnm global_heap_var, MemoryModelExtras.extended_heap_ty, NoSyn)),
           (false, NONE, (bnm (global_var phantom_state_name), pmstate_ty, NoSyn)),
           (false, NONE, (bnm (global_var ghost_state_name), gstate_ty, NoSyn))] @
          map (fn (nm as {isa_name,...}, ty, _, _) =>
                  (false, SOME nm, (bnm (global_var (MString.dest isa_name)), ty, NoSyn)))
              nsglobs @
          (if null owners then []
           else [(false, NONE, (bnm (global_var owned_by_fn_name), nat, NoSyn))])
      (*val thy =
          Record.add_record {overloaded=false}
                            ([], bnm NameGeneration.global_rcd_name) NONE
                            (map_filter (fn (true, _, _) => NONE | (_, _, x) => SOME x) gflds) thy*)
      val fullrecname = Sign.intern_type thy NameGeneration.global_ext_type
      val thy'' = (*MemoryModelExtras.check_global_record_type fullrecname*) thy
    in
      (thy'', locale_params owners, (bnm NameGeneration.global_rcd_name, gflds))
    end

    val lvars = (true,
                 (simple global_exn_var_name,
                  c_exntype_ty, NONE,
                  Local "cparser'internal")) :: map (pair false) lvars0

    (* In the past, the first variable named `x` got its own field named
       `x_'` in the local variables record. If there was another local later in
       the source in another function, also named `x` but of a different type
       `T`, then it would be put in a record field named `x___T_'`. Since this
       was source-order-dependent, we changed the record to only contain the
       full, type-qualified names.

       Of course, a lot of proofs were written under the "some names short,
       other names long" convention, and it's a very useful shorthand for e.g.
       all the `int i` loop index variables, so we recreate those aliases here.

       This works because of how record syntax is implemented. It looks up the
       access/update functions *by string* instead of by checking the context,
       so as long as appropriately named definitions are in scope it'll "just
       work". *)
    fun mk_locals_aliases thy =
        let
          (* Returns a list of `(name, target)` pairs. We want to use the
             `definition` command to alias `target` with `name`. For example, if
             `unsigned x` and `int x` appear in the source (in that order), the
             output should include

             - `(x_', x___unsigned_')`, and
             - `(x_'_update, x___unsigned_'_update)`

             but shouldn't include anything for the `int` case. *)
          fun map_aliases seen vs =
              case vs of
                [] => []
              | (_, ({src_name, isa_name = mangled_name, alias, ...}, _, _, _)) :: rest =>
                  let
                    val acc = HoarePackage.varname (MString.dest mangled_name)
                    val acc_alias = HoarePackage.varname src_name

                    val upd = acc ^ Record.updateN
                    val upd_alias = acc_alias ^ Record.updateN

                    val pairs = [(acc_alias, acc), (upd_alias, upd)]
                  in
                    if not alias orelse member (op =) seen src_name
                    then map_aliases seen rest
                    else pairs @ map_aliases (src_name :: seen) rest
                  end
          val aliases = map_aliases [] lvars
          fun define_alias (alias, target) thy =
              let
                (*val target =
                    Long_Name.qualify NameGeneration.local_rcd_name target
                    |> Proof_Context.read_const {proper = false, strict = false}
                        (Proof_Context.init_global thy)*)
                val alias =
                    Binding.qualify false NameGeneration.local_rcd_name
                      (Binding.make (alias, @{here}))
              in
                thy(*Sign.add_abbrev "" (alias, target) thy |> snd*)
              end
        in
          thy |> fold define_alias aliases
        end
    fun mk_locals_rcd thy =
        let
            (* the state information accumulated so far allows for local
               variables of the same name and type to be declared in different
               functions.  When we come to make an Isabelle record definition
               we want to have just one field of the given name *)
            fun map_elim_name seen =
               fn [] => []
                | (b, (nm0 as {isa_name = nm,...}, ty, _, _)) :: rest => let
                    val nm' = HoarePackage.varname (MString.dest nm)
                    val seen_nm = member (op =) seen nm'
                  in
                    (seen_nm, if b then NONE else SOME nm0, (bnm nm',ty,NoSyn))
                    :: map_elim_name (if seen_nm then seen else (nm'::seen)) rest
                  end
            val lflds = map_elim_name [] lvars
            val _ = pretty_recdef thy "myvars" lvars0
            val thy = (*Record.add_record {overloaded=false}
                      ([("'g",["HOL.type"])], bnm NameGeneration.local_rcd_name)
                      (SOME([TFree("'g", ["HOL.type"])], "StateSpace.state"))
                      (map_filter (fn (true, _, _) => NONE | (_, _, x) => SOME x) lflds)*) thy
        in
          ( thy
          , fn _ => Sign.intern_type thy NameGeneration.local_rcd_name
          , (bnm NameGeneration.local_rcd_name, lflds))
        end
    val (thy, _, local_rcd) = mk_locals_rcd thy
    val thy = mk_locals_aliases thy
    val (thy, globs, global_rcd) = mk_globals_rcd thy
  in
    (thy, map #2 lvars @ gvars, globs, local_rcd, global_rcd)
  end
in
  declare_vars thy
end

type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table

fun mk_mungedb l = let
  open CNameTab
  fun foldthis ((nmi,ty,cty,vsort), tab) = let
    val fnm_opt = case vsort of Local s => SOME s | _ => NONE
  in
    update ({varname = #isa_name nmi, fnname = fnm_opt},
            (#isa_name nmi, ty, cty,vsort))
           tab
  end
in
  List.foldl foldthis empty l
end

structure csenvData = Theory_Data(
  type T = csenv Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_csenv (s,cse) =
    csenvData.map (Symtab.update(s,cse))
fun get_csenv thy file = 
  Symtab.lookup (csenvData.get thy)
                (IsarPreInstall.mk_thy_relative' (IsarPreInstall.parse_file' file) thy |> #2)
fun get_csenv' thy file = 
  Symtab.lookup (csenvData.get thy)
                file

structure ghostData = Theory_Data(
  type T = typ Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_ghostty (s, ty) =
    ghostData.map (Symtab.update(s,ty))
val get_ghostty = Symtab.lookup o ghostData.get

structure mungeDBs = Theory_Data(
  type T = mungedb Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_mungedb (s, ty) = mungeDBs.map (Symtab.update (s,ty))
val get_mungedb = Symtab.lookup o mungeDBs.get

fun get_globals_data statety globty thy = let
    val acc = Sign.intern_const thy "globals"
    val upd = Sign.intern_const thy (suffix Record.updateN "globals")
    val acc = Const (acc, statety --> globty)
    val upd = Const (upd, (globty --> globty) --> statety --> statety)
    val (flds, _) = Record.get_recT_fields thy globty
  in {acc = acc, upd = upd, fields = flds} end

fun get_standard_globals statety globty thy = let
    val data = get_globals_data statety globty thy
    fun fld nm = let
        val flds = filter (fn (fnm, ty) => Long_Name.base_name fnm = nm)
          (#fields data)
        val (fldnm, ty) = case flds of [v] => v
          | [] => error ("could not find " ^ nm ^ " in global fields.")
          | _ => error ("multiple match for " ^ nm ^ " in global fields.")
        val acc = Const (fldnm, globty --> ty)
        val upd = Const (fldnm ^ Record.updateN,
            (ty --> ty) --> globty --> globty)
        val acc' = Abs ("s", statety, acc $ (#acc data $ Bound 0))
        val upd' = Abs ("u", ty --> ty, #upd data $ (upd $ Bound 0))
      in ((acc, upd), (acc', upd')) end
  in {hp = fld global_heap_var,
    phantom = fld (global_var phantom_state_name),
    ghost = fld (global_var ghost_state_name)}
  end

end (* struct *)

(* the string "local variables:" that appears a few lines above this was
   confusing emacs.  By adding the form-feed character below, I ensure that
   this no longer happens.  In other words, don't delete the form-feed! *)


(* Local variables: *)
(* End: *)
