(*****************************************************************************
 * MonadicPrograms.thy --- a basic testing theory for programs.
 * Burkhart Wolff and Chantal Keller, LRI, Univ. Paris-Sud, France
 ******************************************************************************)

chapter \<open>The Clean Language\<close>
text\<open>Pronounce : "C lean".\<close>

theory Clean
  imports Symbex_MonadSE
          "~~/src/HOL/Eisbach/Eisbach"
  keywords "global_vars" "local_vars" :: thy_decl 
(*
     and "funct" :: thy_decl

     and "pre" "post" (* "local_vars" *)
     and "returns" 
     and "end_funct" :: thy_goal
*)
begin
  
text\<open>Clean is a minimalistic imperative language 
with C-like control-flow operators based on a shallow embedding into the
SE exception Monad theory formalized in @{theory "Clean.MonadSE"}. It comprises:
\begin{itemize}
\item C-like control flow with \verb+break+ and \verb+return+.
\item global variables.
\item function calls (seen as Monad-executions) with side-effects, recursion
      and local variables.
\item parameters are modeled via functional abstractions 
      (functions are Monads ...); a passing of parameters to local variables
      might be added later.
\item parametric polymorphism might be added later; at present, states are
      restricted to be monmorphic.
\item cartouche syntax for update operations.
\end{itemize}\<close>
  
  
chapter \<open>Proof of concept for a monadic symbolic execution calculus for WHILE programs\<close>


section\<open> Control-States  \<close>
  
record  control_state = 
            break_status  :: bool
            return_status :: bool

ML\<open> 
fun typ_2_string_raw (Type(s,S)) = 
        let  val h = if null S then "" else enclose "(" ")" (commas (map typ_2_string_raw S)) ;
        in h ^ s end
   |typ_2_string_raw (TFree(s,_))  = s 
   |typ_2_string_raw (TVar((s,n),_))  = s^(Int.toString n) ;

typ_2_string_raw @{ typ "('a) control_state_ext"}
\<close>


(* break quites innermost while or for, return quits an entire execution sequence. *)  
definition break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := True \<rparr>))"
  
definition unset_break_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "unset_break_status \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := False \<rparr>))"

definition set_return :: "'\<alpha> \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "set_return x = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := True \<rparr>))"
    
definition unset_return_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "unset_return_status  = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := False \<rparr>))"
    
definition exec_stop :: "('\<sigma>_ext) control_state_ext \<Rightarrow> bool"
  where   "exec_stop = (\<lambda> \<sigma>. break_status \<sigma> \<or> return_status \<sigma> )"

text\<open> A "lifter" that embeds a state transformer into the state-exception monad. \<close>

consts syntax_assign :: "('\<alpha>  \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> term" (infix ":=" 60)

definition assign :: "(('\<sigma>_ext) control_state_scheme  \<Rightarrow> 
                       ('\<sigma>_ext) control_state_scheme) \<Rightarrow> 
                       (unit,('\<sigma>_ext) control_state_scheme)MON\<^sub>S\<^sub>E"
  where   "assign f = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>) else Some((), f \<sigma>))"

(* todo: rename assign to trans2mon combinator; since it will be used for calls as well *)

fun      assign_global :: "(('a  \<Rightarrow> 'a ) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where "assign_global upd rhs = assign(\<lambda>\<sigma>. ((upd) (%_. rhs \<sigma>)) \<sigma>)"


fun      map_hd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" 
  where "map_hd f [] = []"
      | "map_hd f (a#S) = f a # S"


fun      assign_local :: "(('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where "assign_local upd rhs = assign(\<lambda>\<sigma>. ((upd o map_hd) (%_. rhs \<sigma>)) \<sigma>)"


definition block\<^sub>C :: "  (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E  
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "block\<^sub>C push core pop \<equiv> (          \<comment> \<open>assumes break and return unset \<close> 
                                   push ;-   \<comment> \<open>create new instances of local variables \<close> 
                                   core ;-   \<comment> \<open>execute the body \<close>
                                   unset_break_status ;-    \<comment> \<open>unset a potential break \<close>
                                   unset_return_status;-    \<comment> \<open>unset a potential return break \<close>
                                   (x \<leftarrow> pop;           \<comment> \<open>restore previous local var instances \<close>
                                    unit\<^sub>S\<^sub>E(x)))"        \<comment> \<open>yield the return value \<close>
    


definition call_0\<^sub>C :: "('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_0\<^sub>C M = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M \<sigma>)"

definition call_1\<^sub>C :: "( '\<alpha> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_1\<^sub>C M A\<^sub>1 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) \<sigma>)"


definition call_2\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_2\<^sub>C M A\<^sub>1 A\<^sub>2 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) \<sigma>)"

definition call_3\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow>  '\<gamma> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<gamma>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_3\<^sub>C M A\<^sub>1 A\<^sub>2 A\<^sub>3 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) 
                                                   else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) (A\<^sub>3 \<sigma>) \<sigma>)"

(* and 4 and 5 and ... *)                        

definition if_C :: "[('\<sigma>_ext) control_state_ext \<Rightarrow> bool, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "if_C c E F = (\<lambda>\<sigma>. if exec_stop \<sigma> 
                              then Some(undefined, \<sigma>)  \<comment> \<open>state unchanged, return arbitrary\<close>
                              else if c \<sigma> then E \<sigma> else F \<sigma>)"     

syntax    (xsymbols)
          "_if_SECLEAN" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>C _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>C cond then T1 else T2 fi)" == "CONST Clean.if_C cond T1 T2"

          
          
definition while_C :: "(('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "while_C c B \<equiv> (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>)
                               else ((MonadSE.while_SE (\<lambda> \<sigma>. \<not>exec_stop \<sigma> \<and> c \<sigma>) B) ;- 
                                     unset_break_status) \<sigma>)"
  
syntax    (xsymbols)
          "_while_C" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>C _ do _ od)" [8,8]8)
translations 
          "while\<^sub>C c do b od" == "CONST Clean.while_C c b"

    
section\<open> A Specialized Representation of States based on Records) \<close>

ML\<open>

structure StateMgt_core = 
struct

val control_stateT = Syntax.parse_typ @{context} "control_state"
val control_stateTE = @{typ "('\<sigma>_ext)control_state_ext"};

fun control_state_extT t = Type(@{type_name "Clean.control_state.control_state_ext"}, [t])

fun optionT t = Type(@{type_name "Option.option"},[t]);
fun MON_SE_T res state = state --> optionT(HOLogic.mk_prodT(res,state));

fun merge_control_stateT (@{typ "control_state"},t) = t
   |merge_control_stateT (t, @{typ "control_state"}) = t
   |merge_control_stateT (t, t') = if (t = t') then t else error"can not merge CLEAN state"

datatype var_kind = global_var of typ | local_var of typ

fun type_of(global_var t) = t | type_of(local_var t) = t

type state_field_tab = var_kind Symtab.table

structure Data = Generic_Data
(
  type T       = (state_field_tab * typ) 
  val  empty   = (Symtab.empty,control_stateT)
  val  extend  = I
  fun  merge((s1,t1),(s2,t2))  = (Symtab.merge (op =)(s1,s2),merge_control_stateT(t1,t2))
);


val get_data        = Data.get o Context.Proof;
val map_data        = Data.map;
val get_data_global = Data.get o Context.Theory;
val map_data_global = Context.theory_map o map_data;

val get_state_type             = snd o get_data
val get_state_type_global      = snd o get_data_global
val get_state_field_tab        = fst o get_data
val get_state_field_tab_global = fst o get_data_global
fun upd_state_type f           = map_data (fn (tab,t) => (tab, f t))
fun upd_state_type_global f    = map_data_global (fn (tab,t) => (tab, f t))

fun fetch_state_field (ln,X) = let val a::b:: _  = rev (Long_Name.explode ln) in ((b,a),X) end;

fun filter_name name ln = let val ((a,b),X) = fetch_state_field ln
                          in  if a = name then SOME((a,b),X) else NONE end;

fun filter_attr_of name thy = let val tabs = get_state_field_tab_global thy
                              in  map_filter (filter_name name) (Symtab.dest tabs) end;

fun is_program_variable name thy = Symtab.defined((fst o get_data_global) thy) name

fun is_global_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(global_var _) => true
                                           | _ => false

fun is_local_program_variable name thy = not(is_global_program_variable name thy)

fun declare_state_variable_global f field thy  =  
             let val Const(name,ty) = Syntax.read_term_global thy field
             in  (map_data_global (apfst (Symtab.update_new(name,f ty))) (thy)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

fun declare_state_variable_local f field ctxt  = 
             let val Const(name,ty) = Syntax.read_term_global  (Context.theory_of ctxt) field
             in  (map_data (apfst (Symtab.update_new(name,f ty)))(ctxt)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

end

\<close>



ML\<open>
(* HOLogic extended *)

fun mk_None ty = let val none = \<^const_name>\<open>Option.option.None\<close>
                     val none_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(none, none_ty)
                end;

fun mk_Some t = let val some = \<^const_name>\<open>Option.option.Some\<close> 
                    val ty = fastype_of t
                    val some_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(some, some_ty) $ t
                end;

fun dest_listTy (Type(\<^type_name>\<open>List.list\<close>, [T])) = T;

fun mk_hdT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.hd\<close>, ty --> (dest_listTy ty)) $ t end

fun mk_tlT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.tl\<close>, ty --> ty) $ t end


fun  mk_undefined (@{typ "unit"}) = Const (\<^const_name>\<open>Product_Type.Unity\<close>, \<^typ>\<open>unit\<close>)
    |mk_undefined t               = Const (\<^const_name>\<open>HOL.undefined\<close>, t)

fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);

fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;


(* the meat *)
local open StateMgt_core



    fun get_result_value_conf name thy = 
            let val  S = filter_attr_of name thy
            in  hd(filter (fn ((a,b),c) => b = "result_value") S) 
                handle _ => error("internal error: get_result_value_conf") end; 


    fun mk_lookup_result_value_term name sty thy =
        let val ((prefix,name),local_var(Type("fun", [_,ty]))) = get_result_value_conf name thy;
            val long_name = Sign.intern_const thy (prefix^"."^name)
            val term = Const(long_name, sty --> ty)
        in  mk_hdT (term $ Free("\<sigma>",sty)) end


    fun  map_to_update sty is_pop thy ((struct_name, attr_name), local_var (Type("fun",[_,ty]))) term = 
           let val tlT = if is_pop then Const(\<^const_name>\<open>List.tl\<close>, ty --> ty)
                         else Const(\<^const_name>\<open>List.Cons\<close>, dest_listTy ty --> ty --> ty)
                              $ mk_undefined (dest_listTy ty)
               val update_name = Sign.intern_const  thy (struct_name^"."^attr_name^"_update")
           in (Const(update_name, (ty --> ty) --> sty --> sty) $ tlT) $ term end
       | map_to_update _ _ _ ((_, _),_) _ = error("internal error map_to_update")     

    fun mk_local_state_name binding = Binding.prefix_name "local_" (Binding.suffix_name "_state" binding)  
    fun mk_global_state_name binding = Binding.prefix_name "global_" (Binding.suffix_name "_state" binding)  

    in fun construct_update is_pop binding sty thy = 
           let val long_name = Binding.name_of( binding)
               val _ = writeln ("construct_update : "^long_name)
               val attrS = StateMgt_core.filter_attr_of long_name thy
           in  fold (map_to_update sty is_pop thy) (attrS) (Free("\<sigma>",sty)) end

    fun cmd (decl, spec, prems, params) = #2 oo Specification.definition' decl params prems spec


val SPY = Unsynchronized.ref (Bound 0)
val SPY1 = Unsynchronized.ref (Binding.empty)
val SPY2 =  Unsynchronized.ref (@{typ "unit"})
val SPY3 =  Unsynchronized.ref (@{typ "unit"})

    fun mk_push_name binding = Binding.prefix_name "push_" binding

    fun push_eq binding  name_op rty sty lthy = 
             let val mty = MON_SE_T rty sty 
                 val thy = Proof_Context.theory_of lthy
                 val term = construct_update false binding sty thy
             in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                             mk_Some ( HOLogic.mk_prod (mk_undefined rty,term)))
                              
             end;

    fun mk_push_def binding sty lthy =
        let val name_pushop =  mk_push_name binding
            val rty = \<^typ>\<open>unit\<close>
            val eq = push_eq binding  (Binding.name_of name_pushop) rty sty lthy
            val mty = StateMgt_core.MON_SE_T rty sty 
            val args = (SOME(name_pushop,NONE (* SOME mty *),NoSyn), (Binding.empty_atts,eq),[],[])
            val lthy' = cmd args true lthy
        in lthy'
        end;

    fun mk_pop_name binding = Binding.prefix_name "pop_"  binding

    fun pop_eq  binding name_op rty sty lthy = 
             let val mty = MON_SE_T rty sty 
                 val thy = Proof_Context.theory_of lthy
                 val res_access = mk_lookup_result_value_term (Binding.name_of binding) sty thy
                 val term = construct_update true binding  sty thy                 
             in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                             mk_Some ( HOLogic.mk_prod (res_access,term)))
                              
             end;


    fun mk_pop_def binding rty sty lthy = 
        let val mty = StateMgt_core.MON_SE_T rty sty 
            val name_op =  mk_pop_name binding
            val _ = writeln ("mk_pop_def : "^ Binding.name_of name_op )
            val eq = pop_eq binding (Binding.name_of name_op) rty sty lthy
            val _ = (SPY:=eq)
            val args = (SOME(name_op,NONE(* SOME mty *),NoSyn),(Binding.empty_atts,eq),[],[])
        in cmd args true lthy
        end;



fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
       (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

fun add_record_cmd0 read_fields overloaded is_global_kind (raw_params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    fun lift (a,b,c) =  (a, HOLogic.listT b, c)
    val fields' = if is_global_kind then fields else map lift fields
    val params' = map (Proof_Context.check_tfree ctxt3) params;
    val declare = StateMgt_core.declare_state_variable_global
    fun upd_state_typ thy = let val ctxt = Proof_Context.init_global thy
                                val name = Binding.name_of binding
                                val _ = writeln ("upd_state_typ XXX"^name)
                                val ty = Syntax.parse_typ ctxt name
                            in  StateMgt_core.upd_state_type_global(K ty)(thy) end
    fun insert_var ((f,_,_), thy) =           
            if is_global_kind   
            then declare StateMgt_core.global_var (Binding.name_of f) thy
            else declare StateMgt_core.local_var  (Binding.name_of f) thy
    fun define_push_pop thy = 
            if not is_global_kind 
            then let val ctxt = Proof_Context.init_global thy;
                     val name = Binding.name_of binding
                     val ty_repr1 = "'a "^name^"_scheme"
                     val ty_bind =  Binding.prefix_name "'a " (Binding.suffix_name "_scheme" binding)
                     val ty_repr2 = Binding.name_of ty_bind
                     val _ = writeln ("define_push_pop XXX"^name^":"^ty_repr1^":"^ty_repr2)
                     val sty = Syntax.parse_typ ctxt (ty_repr1)
                     val rty = dest_listTy (#2(hd(rev fields')))
                     val _ = (SPY1 := binding)
                     val _ = (SPY2 := sty)
                     val _ = (SPY3 := rty)
                 in thy

                    |> Named_Target.theory_map (mk_push_def binding sty) 
                    |> Named_Target.theory_map (mk_pop_def  binding rty sty) 
                                                            
                 end
            else thy
  in thy |> Record.add_record overloaded (params', binding) parent fields' 
         |> (fn thy =>  List.foldr insert_var (thy) (fields'))
         |> upd_state_typ
         |> define_push_pop 
  end;



fun typ_2_string_raw (Type(s,[])) = s
   |typ_2_string_raw (Type(s,_)) = 
                         error ("Illegal parameterized state type - not allowed in CLEAN:"  ^ s) 
   |typ_2_string_raw _ = error "Illegal parameterized state type - not allowed in CLEAN." 
                                  

fun new_state_record0 add_record_cmd is_global_kind (((raw_params, binding), res_ty), raw_fields) thy =
    let val _ = writeln ("<Z " ^ (typ_2_string_raw (StateMgt_core.get_state_type_global thy)))
        val binding = if is_global_kind 
                      then mk_global_state_name binding
                      else mk_local_state_name binding
        val raw_parent = SOME(typ_2_string_raw (StateMgt_core.get_state_type_global thy))
        val pos = Binding.pos_of binding
        fun upd_state_typ thy = let val ctxt = Proof_Context.init_global thy
                                    val name:bstring = Binding.name_of binding 
                                    val _ = writeln ("<ZZ " ^ name)
                                    val ty = Syntax.parse_typ ctxt name (* or: Binding.print name ? *)
                                in  StateMgt_core.upd_state_type_global(K ty)(thy) end
        val raw_fields' = case res_ty of 
                            NONE => raw_fields
                          | SOME res_ty => raw_fields @ [(Binding.make("result_value",pos),res_ty, NoSyn)]
    in  thy |> add_record_cmd {overloaded = false} is_global_kind 
                              (raw_params, binding) raw_parent raw_fields' 
            |> upd_state_typ 

    end

val add_record_cmd = add_record_cmd0 read_fields;
val add_record_cmd' = add_record_cmd0 pair;

val new_state_record  = new_state_record0 add_record_cmd
val new_state_record' = new_state_record0 add_record_cmd'

val _ =
  Outer_Syntax.command @{command_keyword global_vars} "define global state record"
    ((Parse.type_args_constrained -- Parse.binding)
    -- Scan.succeed NONE
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record true));

val _ =
  Outer_Syntax.command @{command_keyword local_vars} "define local state record"
    ((Parse.type_args_constrained -- Parse.binding) 
    -- (Parse.typ >> SOME)
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record false));
end
\<close>


section\<open>Monadic Presentation of Assignments (based on Extensible Records) \<close>


text\<open> ... and we provide syntactic sugar via cartouches \<close>
text\<open> Basic Symbolic execution rules. As they are equalities, they can also
be used as program optimization rules. \<close>

lemma non_exec_assign  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success)

lemma non_exec_assign'  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)

lemma exec_assign  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success)     

lemma exec_assign'  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)     

lemma non_exec_assign_global  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
by(simp add: non_exec_assign assms)

lemma non_exec_assign_global'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
  by (metis (full_types) assms bind_SE'_def non_exec_assign_global)


lemma exec_assign_global  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_def assms exec_bind_SE_success)

lemma exec_assign_global'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add:  assign_def assms exec_bind_SE_success bind_SE'_def)

lemma non_exec_assign_local  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by(simp add: non_exec_assign assms)

lemma non_exec_assign_local'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_local upd rhs;- M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by (metis assms bind_SE'_def non_exec_assign_local)


lemma exec_assign_local  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_def assms exec_bind_SE_success)

lemma exec_assign_local'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add:  assign_def assms exec_bind_SE_success bind_SE'_def)


lemmas exec_assignD = exec_assign[THEN iffD1]
thm exec_assignD

lemmas exec_assignD' = exec_assign'[THEN iffD1]

lemma non_exec_call_0  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_0\<^sub>C_def valid_SE_def)

lemma non_exec_call_0'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_0\<^sub>C M;- M') = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def non_exec_call_0)


lemma exec_call_0  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_0\<^sub>C_def exec_bind_SE_success)

lemma exec_call_0'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_0\<^sub>C M;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_0)




lemma non_exec_call_1  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> (call_1\<^sub>C M A\<^sub>1); M')) = (\<sigma> \<Turnstile> M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_1\<^sub>C_def valid_SE_def)

lemma non_exec_call_1'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_1\<^sub>C M A\<^sub>1;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_1)

lemma exec_call_1  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_1\<^sub>C M A\<^sub>1; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_1\<^sub>C_def exec_bind_SE_success)

lemma exec_call_1'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_1\<^sub>C M A\<^sub>1;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_1)


lemma non_exec_call_2  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2); M')) = (\<sigma> \<Turnstile> M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_2\<^sub>C_def valid_SE_def)

lemma non_exec_call_2'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_2)

lemma exec_call_2  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_2\<^sub>C M A\<^sub>1 A\<^sub>2; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_2\<^sub>C_def exec_bind_SE_success)

lemma exec_call_2'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M')) = (\<sigma> \<Turnstile> M')"
  by (simp add: assms bind_SE'_def exec_call_2)


lemma exec_If\<^sub>C_If\<^sub>S\<^sub>E  : 
assumes "\<not> exec_stop \<sigma>"
shows  " ((if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi))\<sigma> = ((if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) \<sigma> "
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def
  by (simp add: assms bind_SE_def if_C_def)
    
    
lemma valid_exec_If\<^sub>C  : 
assumes "\<not> exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M)"
  by (meson assms exec_If\<^sub>C_If\<^sub>S\<^sub>E valid_bind'_cong)


      
lemma exec_If\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
    by (simp add: assms if_C_def)
    
lemma exec_While\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (while\<^sub>C P do B\<^sub>1 od);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding while_C_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
  apply simp using assms by blast    
    
text\<open> Syntactic sugar via cartouches \<close>

ML \<open>
  local
    fun app_sigma db tm ctxt = case tm of
        Const(name, _) => if StateMgt_core.is_program_variable name (Proof_Context.theory_of ctxt) 
                          then tm $ (Bound db) (* lifting *)
                          else tm              (* no lifting *)
      | Free _ => tm
      | Var _ => tm
      | Bound _ => tm
      | Abs (x, a, tm') => Abs(x, a, app_sigma (db+1) tm' ctxt)
      | t1 $ t2 => (app_sigma db t1 ctxt) $ (app_sigma db t2 ctxt)
      
    fun mk_assign t1 ctxt = case t1 of
        (Const("_type_constraint_",_)) $ (Const (name,ty))    => 
                          if StateMgt_core.is_program_variable name (Proof_Context.theory_of ctxt) 
                          then Const(name^Record.updateN, ty)
                          else raise TERM ("mk_assign", [t1])
      | _ => raise TERM ("mk_assign", [t1])

    fun transform_term tm ctxt =
            case tm of
               Const("Clean.syntax_assign",_) $ t1 $ t2 =>
                  Const(@{const_name "assign"},dummyT)
                  $ (Abs ("\<sigma>", dummyT, ((mk_assign t1 ctxt) 
                                      $ (absdummy dummyT (app_sigma 1 t2 ctxt)) 
                                      $ (Bound 0))))
             | _ => Abs ("\<sigma>", dummyT, app_sigma 0 tm ctxt)
  in
    fun string_tr ctxt (content:(string * Position.T) -> (string * Position.T) list) (args:term list) : term =
      let fun err () = raise TERM ("string_tr", args) 
      in
        (case args of
          [(Const (@{syntax_const "_constrain"}, _)) $ (Free (s, _)) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) =>
              let val txt = Symbol_Pos.implode(content (s,pos))
                  val tm = Syntax.parse_term ctxt txt
                  val tr = transform_term tm ctxt
                  val ct = Syntax.check_term ctxt tr
              in
                ct
              end
            | NONE => err ())
        | _ => err ())
      end
  end
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> string"  ("_")

parse_translation \<open>
  [(@{syntax_const "_cartouche_string"},
    (fn ctxt => (string_tr ctxt ((Symbol_Pos.cartouche_content : Symbol_Pos.T list -> Symbol_Pos.T list)
                 o (Symbol_Pos.explode : string * Position.T -> Symbol_Pos.T list)))) )]
\<close>


section\<open> Tactic Support: we use Eisbach to automate the process. \<close>

txt\<open> Necessary prerequisite: turning ematch and dmatch into a proper Isar Method. \<close>
(* TODO : this code shoud go to TestGen Method setups *)
ML\<open>
val _ =
  Theory.setup
   (Method.setup @{binding ematch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(ematch_tac ctxt rules)) ))) 
      "fast elimination matching" #>
    Method.setup @{binding dmatch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(dmatch_tac ctxt rules)) ))) 
       "fast destruction matching" #>
    Method.setup @{binding match}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(match_tac ctxt rules)) )))
       "resolution based on fast matching")
\<close>

txt\<open> Various tactics for various coverage criteria \<close>

definition while_k :: "nat \<Rightarrow> (('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
where     "while_k _ \<equiv> while_C"

lemma while_k_SE : "while_C = while_k k"
by (simp only: while_k_def)
    
    
lemma if\<^sub>C_cond_cong : "f \<sigma> = g \<sigma> \<Longrightarrow> 
                           (if\<^sub>C f then c else d fi) \<sigma> = 
                           (if\<^sub>C g then c else d fi) \<sigma>"
  unfolding if_C_def
   by simp 
   
     

lemma while\<^sub>C_skip [simp]: "(while\<^sub>C (\<lambda> x. False) do c od) = skip\<^sub>S\<^sub>E"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def
  apply auto
  unfolding exec_stop_def skip\<^sub>S\<^sub>E_def unset_break_status_def bind_SE'_def unit_SE_def bind_SE_def
  by simp
  

lemma break_assign_skip [simp]: "break ;- assign f = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def bind_SE'_def   bind_SE_def
  by auto



lemma break_if_skip [simp]: "break ;- (if\<^sub>C b then c else d fi) = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def if_C_def bind_SE'_def   bind_SE_def
  by auto
    
                       
lemma break_while_skip [simp]: "break ;- (while\<^sub>C b do c od) = break"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def bind_SE'_def bind_SE_def break_def exec_stop_def
  by simp

    
lemma unset_break_idem [simp] : 
 "( unset_break_status ;- unset_break_status ;- M) = (unset_break_status ;- M)"
  apply(rule ext)  unfolding unset_break_status_def bind_SE'_def bind_SE_def by auto
    
    
method bound_while for n::nat = (simp only: while_k_SE [of n])


(* this still holds ... *)
lemma exec_while\<^sub>C : 
"(\<sigma> \<Turnstile> ((while\<^sub>C b do c od) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while\<^sub>C b do c od) ;- unset_break_status else skip\<^sub>S\<^sub>E fi)  ;- M))"
proof (cases "exec_stop \<sigma>")
  case True
  then show ?thesis 
    by (simp add: True exec_If\<^sub>C' exec_While\<^sub>C')
next
  case False
  then show ?thesis
    proof (cases "\<not> b \<sigma>")
      case True
      then show ?thesis
        apply(subst valid_bind'_cong)
        using \<open>\<not> exec_stop \<sigma>\<close> apply simp_all
        apply (auto simp: skip\<^sub>S\<^sub>E_def unit_SE_def)
          apply(subst while_C_def, simp)
         apply(subst bind'_cong)
         apply(subst MonadSE.while_SE_unfold)
          apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. False"])
          apply simp_all
        apply(subst if\<^sub>C_cond_cong [of _ _ "\<lambda>_. False"], simp add: )
        apply(subst exec_If\<^sub>C_If\<^sub>S\<^sub>E,simp_all)
        by (simp add: exec_stop_def unset_break_status_def)
    next
      case False
      have * : "b \<sigma>"  using False by auto
      then show ?thesis
           unfolding while_k_def 
           apply(subst  while_C_def)
           apply(subst  if_C_def)
           apply(subst  valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
           apply(subst  (2) valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
            apply(subst MonadSE.while_SE_unfold)
            apply(subst valid_bind'_cong)
            apply(subst bind'_cong)
             apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. True"])
              apply(simp_all add:   \<open>\<not> exec_stop \<sigma>\<close> )
            apply(subst bind_assoc', subst bind_assoc')
            proof(cases "c \<sigma>")
              case None
              then show "(\<sigma> \<Turnstile> c;-((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c;-(while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                by (simp add: bind_SE'_def exec_bind_SE_failure)
            next
              case (Some a)
              then show "(\<sigma> \<Turnstile> c ;- ((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c ;- (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                apply(insert \<open>c \<sigma> = Some a\<close>, subst (asm) surjective_pairing[of a])
                apply(subst exec_bind_SE_success2, assumption)
                apply(subst exec_bind_SE_success2, assumption)
                proof(cases "exec_stop (snd a)")
                  case True
                  then show "(snd a \<Turnstile>((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                       by (metis (no_types, lifting) bind_assoc' exec_While\<^sub>C' exec_skip if_SE_D2' 
                                                  skip\<^sub>S\<^sub>E_def while_SE_unfold)
                next
                  case False
                  then show "(snd a \<Turnstile> ((while\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                          unfolding  while_C_def
                          by(subst (2) valid_bind'_cong,simp)(simp)
                qed       
            qed  
    qed
qed
(* ... although it is, oh my god, amazingly complex to prove. *)
  
corollary exec_while_k : 
"(\<sigma> \<Turnstile> ((while_k (Suc n) b c) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while_k n b c) ;- unset_break_status else skip\<^sub>S\<^sub>E fi)  ;- M))"
  by (metis exec_while\<^sub>C while_k_def)
    

lemmas exec_while_kD = exec_while_k[THEN iffD1]

named_theorems memory_theory
method memory_theory = (simp only: memory_theory MonadSE.bind_assoc')
method norm = (auto dest!: assert_D)

(* Remark: if instead of a recursive call, we use "+", this corresponds to recursing only on the
   first goal, and thus does not work with nested loops *)
method loop_coverage_steps methods simp_mid =
  ((ematch assume_E')
    | (ematch if_SE_execE'', simp_mid?)
    | (dmatch exec_while_kD)
    | (dmatch exec_skipD)
    | (dmatch exec_assignD')
  ); (loop_coverage_steps simp_mid)?
method loop_coverage for n::nat methods simp_mid simp_end =
       (bound_while n)?, loop_coverage_steps simp_mid, simp_end?
  
method branch_and_loop_coverage for n::nat uses mt = loop_coverage n memory_theory simp_all
method mcdc_and_loop_coverage for n::nat = loop_coverage n auto auto


(* method mcdc_and_loop_coverage for n::nat = loop_coverage n norm norm *)

method loop_coverage_positive_branch_steps =
  ((ematch assume_E')
    | (ematch if_SE_execE''_pos, memory_theory?)
    | (dmatch exec_while_kD, ematch if_SE_execE'', memory_theory?)
    | (dmatch exec_skipD)
    | (dmatch exec_assignD')
  ); loop_coverage_positive_branch_steps?
method loop_coverage_positive_branch for n::nat =
  (bound_while n)?, loop_coverage_positive_branch_steps, simp_all?

end

  
  