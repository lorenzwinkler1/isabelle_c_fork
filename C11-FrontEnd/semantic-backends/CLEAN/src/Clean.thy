(*****************************************************************************
 * MonadicPrograms.thy --- a basic testing theory for programs.
 * Burkhart Wolff and Chantal Keller, LRI, Univ. Paris-Sud, France
 ******************************************************************************)

chapter {* The Clean Language *}

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
  
  
text{* Clean is a minimalistic imperative language 
with C-like control-flow operators based on a shallow embedding into the
SE exception Monad theory formalized in @{theory "MonadSE"}. It comprises:
\begin{itemize}
\item C-like control flow with \verb+break+ and \verb+return+
\item global variables
\item function calls (seen as Monad-executions) with side-effects, recursion
      and local variables
\item parameters are modeled via functional abstractions 
      (functions are Monads ...); a passing of parameters to local variables
      might be added later
\item cartouche syntax for update operations.
\end{itemize} *}
  
  
chapter {* Proof of concept for a monadic symbolic execution calculus for WHILE programs *}


section\<open> Control-States  \<close>
  
record  control_state = 
          break_val  :: bool
          return_val :: bool
          
typ "('a) control_state_ext"

ML\<open> 
fun typ_2_string_raw (Type(s,S)) = 
        let  val h = if null S then "" else enclose "(" ")" (commas (map typ_2_string_raw S)) ;
        in h ^ s end
   |typ_2_string_raw (TFree(s,_))  = s 
   |typ_2_string_raw (TVar((s,n),_))  = s^(Int.toString n) ;

typ_2_string_raw @{ typ "('a) control_state_ext"}
\<close>


record  mmm = "control_state" +
       df :: "int"

record mmk = "mmm" + dsf :: int 

(* break quites innermost while or for, return quits an entire execution sequence. *)  
definition break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_val := True \<rparr>))"
  
definition unset_break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "unset_break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_val := False \<rparr>))"

definition return :: "'\<alpha> \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "return x = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_val := True \<rparr>))"
    
definition unset_return_val :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "unset_return_val  = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_val := False \<rparr>))"
    
definition exec_stop :: "('\<sigma>_ext) control_state_ext \<Rightarrow> bool"
  where   "exec_stop = (\<lambda> \<sigma>. break_val \<sigma> \<or> return_val \<sigma> )"

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
  where "map_hd f (a#S) = f a # S"


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
                                   unset_break ;-        \<comment> \<open>unset a potential break \<close>
                                   unset_return_val;-    \<comment> \<open>unset a potential return break \<close>
                                   (x \<leftarrow> pop;            \<comment> \<open>restore previous local var instances \<close>
                                    unit\<^sub>S\<^sub>E(x)))"         \<comment> \<open>yield the return value \<close>
    


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
                              then Some(undefined, \<sigma>)  (* state unchanged, return arbitrary *)
                              else if c \<sigma> then E \<sigma> else F \<sigma>)"     

syntax    (xsymbols)
          "_if_SECLEAN" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>C _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>C cond then T1 else T2 fi)" == "CONST Clean.if_C cond T1 T2"

          
          
definition while_C :: "(('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where     "while_C c B \<equiv> (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>)
                                 else ((MonadSE.while_SE (\<lambda> \<sigma>. \<not>exec_stop \<sigma> \<and> c \<sigma>) B) ;- 
                                       unset_break) \<sigma>)"
  
syntax    (xsymbols)
          "_while_C" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>C _ do _ od)" [8,8]8)
translations 
          "while\<^sub>C c do b od" == "CONST Clean.while_C c b"

   
    
section\<open> A Specialized Representation of States based on Records) \<close>

ML{*

structure StateMgt_core = 
struct

val control_stateT = Syntax.parse_typ @{context} "control_state"
val control_stateTE = @{typ "('\<sigma>_ext)control_state_ext"};

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

val get_state_type          = snd o get_data
val get_state_type_global   = snd o get_data_global
fun upd_state_type f        = map_data (fn (tab,t) => (tab, f t))
fun upd_state_type_global f = map_data_global (fn (tab,t) => (tab, f t))


fun is_program_variable name thy = Symtab.defined((fst o get_data_global) thy) name

fun is_global_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(global_var _) => true
                                           | _ => false

fun is_local_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(local_var _) => true
                                           | _ => false

fun declare_state_variable_global f field thy  =  
             let val Const(name,Type("fun",ty::_)) = Syntax.read_term_global thy field
             in  (map_data_global (apfst (Symtab.update_new(name,f ty))) (thy)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

fun declare_state_variable_local f field ctxt  = 
             let val Const(name,Type("fun",ty::_)) = Syntax.read_term_global 
                                                        (Context.theory_of ctxt) field
             in  (map_data (apfst (Symtab.update_new(name,f ty)))(ctxt)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;
(*

fun declare_state_variable_local field ctxt  = (map_data (apfst(fn {tab=t,maxano=x} => 

val Const(name,Type("fun",a::R)) = Syntax.read_term @{context} "tm"
*)
end

*}

ML\<open> Syntax.string_of_typ ; open Term\<close>

ML{* 
local open StateMgt_core in

val S = List.foldr (fn ((f,_,_), thy) 
                    => declare_state_variable_global global_var (Binding.name_of f) thy)  

end
*}

ML\<open>\<close>

ML{*
val SPY = Unsynchronized.ref([]:(binding * typ * mixfix)list)

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

fun add_record_cmd overloaded is_global_kind (raw_params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    val params' = map (Proof_Context.check_tfree ctxt3) params;
    val declare = StateMgt_core.declare_state_variable_global
    fun insert_var ((f,_,_), thy') =           
            if is_global_kind 
            then declare StateMgt_core.global_var (Binding.name_of f) thy'
            else declare StateMgt_core.local_var  (Binding.name_of f) thy'
    val _ = (SPY := fields)
  in thy |> Record.add_record overloaded (params', binding) parent fields 
         |> (fn thy =>  List.foldr insert_var (thy) (fields)) 
  end;


fun typ_2_string_raw (Type(s,[])) = s
   |typ_2_string_raw (Type(s,_)) = error ("Illegal parameterized state type - not allowed in CLEAN:" 
                                          ^ s) 
   |typ_2_string_raw _ = error "Illegal parameterized state type - not allowed in CLEAN." 
                                  

fun new_state_record  is_global_kind (raw_params, binding)  raw_fields thy =
    let val _ = writeln ("<Z " ^ (typ_2_string_raw (StateMgt_core.get_state_type_global thy)))
        val raw_parent = SOME(typ_2_string_raw (StateMgt_core.get_state_type_global thy))
        fun upd_state_typ thy = let val t = Syntax.parse_typ(Proof_Context.init_global thy) 
                                                            (Binding.name_of binding)
                                    val _ = writeln ("Z> "^(typ_2_string_raw t))
                                in  StateMgt_core.upd_state_type_global(K t)(thy) end
    in  thy |> add_record_cmd {overloaded = false} is_global_kind 
                              (raw_params, binding) raw_parent raw_fields 
            |> upd_state_typ
    end

val _ = new_state_record : bool ->
      (string * string option) list * binding ->
        (binding * string * mixfix) list -> theory -> theory

val _ =
  Outer_Syntax.command @{command_keyword global_vars} "define global state record"
    ((Parse.type_args_constrained -- Parse.binding) -- Scan.repeat1 Parse.const_binding
    >> (fn (x, z) => Toplevel.theory (new_state_record true x  z)));

val _ =
  Outer_Syntax.command @{command_keyword local_vars} "define local state record"
    ((Parse.type_args_constrained -- Parse.binding) -- Scan.repeat1 Parse.const_binding
    >> (fn (x, z) => Toplevel.theory (new_state_record false x  z)));


*}

ML\<open>@{command_keyword "global_vars"}\<close>

section\<open>Monadic Presentation of Assignments (based on Records) \<close>


text\<open> ... and we provide syntactic sugar via cartouches \<close>
text\<open> Basic Symbolic execution rules. As they are equalities, they can also
be used as program optimization rules. \<close>

lemma exec_assign  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success)
    
lemma exec_assign'  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = (\<sigma> \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success)     

lemmas exec_assignD = exec_assign[THEN iffD1]

lemmas exec_assignD' = exec_assign'[THEN iffD1]

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
val SPY = Unsynchronized.ref(Bound 0)
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
                  val _ = (SPY := tm)
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
  unfolding exec_stop_def skip\<^sub>S\<^sub>E_def unset_break_def bind_SE'_def unit_SE_def bind_SE_def
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

    
lemma unset_break_idem [simp] : "( unset_break ;- unset_break ;- M) = (unset_break ;- M)"
  apply(rule ext)  unfolding unset_break_def bind_SE'_def bind_SE_def by auto
    
    
method bound_while for n::nat = (simp only: while_k_SE [of n])


(* this still holds ... *)
lemma exec_while\<^sub>C : 
"(\<sigma> \<Turnstile> ((while\<^sub>C b do c od) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while\<^sub>C b do c od) ;- unset_break else skip\<^sub>S\<^sub>E fi)  ;- M))"
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
        using `\<not> exec_stop \<sigma>` apply simp_all
        apply (auto simp: skip\<^sub>S\<^sub>E_def unit_SE_def)
          apply(subst while_C_def, simp)
         apply(subst bind'_cong)
         apply(subst MonadSE.while_SE_unfold)
          apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. False"])
          apply simp_all
        apply(subst if\<^sub>C_cond_cong [of _ _ "\<lambda>_. False"], simp add: )
        apply(subst exec_If\<^sub>C_If\<^sub>S\<^sub>E,simp_all)
        by (simp add: exec_stop_def unset_break_def)
    next
      case False
      have * : "b \<sigma>"  using False by auto
      then show ?thesis
           unfolding while_k_def 
           apply(subst  while_C_def)
           apply(subst  if_C_def)
           apply(subst  valid_bind'_cong)
            apply (simp add: `\<not> exec_stop \<sigma>`)
           apply(subst  (2) valid_bind'_cong)
            apply (simp add: `\<not> exec_stop \<sigma>`)
            apply(subst MonadSE.while_SE_unfold)
            apply(subst valid_bind'_cong)
            apply(subst bind'_cong)
             apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. True"])
              apply(simp_all add:   `\<not> exec_stop \<sigma>` )
            apply(subst bind_assoc', subst bind_assoc')
            proof(cases "c \<sigma>")
              case None
              then show "(\<sigma> \<Turnstile> c;-((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break);-M) =
                         (\<sigma> \<Turnstile> c;-(while\<^sub>C b do c od) ;- unset_break ;- M)"
                by (simp add: bind_SE'_def exec_bind_SE_failure)
            next
              case (Some a)
              then show "(\<sigma> \<Turnstile> c ;- ((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break);-M) =
                         (\<sigma> \<Turnstile> c ;- (while\<^sub>C b do c od) ;- unset_break ;- M)"
                apply(insert `c \<sigma> = Some a`, subst (asm) surjective_pairing[of a])
                apply(subst exec_bind_SE_success2, assumption)
                apply(subst exec_bind_SE_success2, assumption)
                proof(cases "exec_stop (snd a)")
                  case True
                  then show "(snd a \<Turnstile>((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break ;- M)"
                       by (metis (no_types, lifting) bind_assoc' exec_While\<^sub>C' exec_skip if_SE_D2' 
                                                  skip\<^sub>S\<^sub>E_def while_SE_unfold)
                next
                  case False
                  then show "(snd a \<Turnstile> ((while\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break ;- M)"
                          unfolding  while_C_def
                          by(subst (2) valid_bind'_cong,simp)(simp)
                qed       
            qed  
    qed
qed
(* ... although it is, oh my god, amazingly complex to prove. *)
  
corollary exec_while_k : 
"(\<sigma> \<Turnstile> ((while_k (Suc n) b c) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while_k n b c) ;- unset_break else skip\<^sub>S\<^sub>E fi)  ;- M))"
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

  
  