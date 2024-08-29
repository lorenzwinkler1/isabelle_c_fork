theory "Coder_Test_Env_AEnv"
  imports "../src/CleanCoder"
begin



section \<open>Accessors to C-Env\<close>

ML\<open>
fun map_option f (SOME X) = SOME(f X)
   |map_option f NONE     = NONE   

fun lookup_Cid_info (C_env:C_Module.Data_In_Env.T) id = Symtab.lookup(#idents(#var_table C_env)) id

fun is_global_Cid Cenv Cid     = map_option (#global o #3) (lookup_Cid_info Cenv Cid);
fun is_fun_Cid Cenv Cid        = map_option ((fn [C_Ast.CFunDeclr0 _] => true | _ => false) 
                                               o (#params o #3)) 
                                            (lookup_Cid_info Cenv Cid);
fun get_CDeclSpecS_Cid Cenv id = map_option (#ret o #3) (lookup_Cid_info Cenv id);

(* Fundsachen *)
C11_Ast_Lib.encode_positions;
C11_Ast_Lib.decode_positions;
C11_Ast_Lib.toString_abr_string;
C11_Ast_Lib.toString_nodeinfo;

C_Ast.SS_base
\<close>

section \<open>Global Variables, Local Variables, and Local Parameters\<close>
subsection\<open>An Environment Spy\<close>

ML\<open>
val ENV = Unsynchronized.ref (@{C\<^sub>e\<^sub>n\<^sub>v})
fun print_env' s _ stack _ env thy =
  let
    val () = (ENV:=env; writeln ("ENV " ^ C_Env.string_of env))
  in thy end
\<close>

ML\<open>open Position\<close>
setup \<open>ML_Antiquotation.inline @{binding print_env'}
                               (Scan.peek (fn _ => Scan.option Parse.embedded)
                                >> (fn name => ("print_env' "
                                                ^ (case name of NONE => "NONE"
                                                              | SOME s => "(SOME \"" ^ s ^ "\")")
                                                ^ " " ^ ML_Pretty.make_string_fn)))\<close>

subsection\<open>Accessing the C_Env in an Example\<close>

C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a(int b){int c; 
              return c;
              /*@@ \<approx>setup \<open>@{print_env'}\<close> */
              /*@@ highlight */
             }; 
                 
\<close>


ML\<open>
val a_res = lookup_Cid_info (!ENV) "a";
val b_res = lookup_Cid_info (!ENV) "b";
val c_res = lookup_Cid_info (!ENV) "c"
\<close>


(* Problematic : *)
C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a (int b){int b; 
              return b;
              /*@@ highlight */
              /*@@ \<approx>setup \<open>@{print_env'}\<close> */}; 
                 
\<close>
ML\<open>
lookup_Cid_info (!ENV) "a";
lookup_Cid_info (!ENV) "b"
\<close>





section \<open>Global Declarations via CEnv and via the Clean API\<close>

text \<open>
First, we translate the expressions;
we can have binary operators, unary operators, or constants.
The attributs can be constantes or variables. 
In order to simulate the use of variables, we construct a "fake" record local_state
\<close>

global_vars (test)  (*intern label *)
            a     :: "int"

(* creation of a global variable Clean state with "a" *)
ML\<open>val Const(longid_a,Type("fun",[sigma_i, _])) = @{term "a"}; \<close>
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>


(* creation of two declarations with "a" an array and "f" a function *)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]

C\<open> int a[10+12][34][] = 1;
   short int f(int x [][], long double y)
     {int y; x=x;
      /*@@ \<approx>setup \<open>@{print_env'}\<close> */
      /*@@ highlight */}
     ;
      
\<close>

(* binding the resulting C_Env to env_expr *)

ML\<open>val env_expr : C_Module.Data_In_Env.T =  @{C\<^sub>e\<^sub>n\<^sub>v};\<close>

(* messing around with the C identifier "a" and "f" in the env AFTER the translation unit*)
ML\<open>
   val SOME(pos_list,ser,S)    = lookup_Cid_info env_expr "a";
   val SOME(pos_list',ser',S') = lookup_Cid_info env_expr "f";
   val NONE = lookup_Cid_info env_expr "x";
\<close>
(* handy decompositions *)
ML\<open>

local open C_Ast C_Env in

   val [CArrDeclr0 (HH,CArrSize0 (_,CBinary0 X),_),
        CArrDeclr0 (_,CArrSize0  (_,CConst0 Y), _), 
        CArrDeclr0 (_,CNoArrSize0 Z,_)] = #params S
   val [CFunDeclr0 (Right([CDecl0 (A,A' as [((Some (CDeclr0 (_,TT,_,_,_)),_),_)],_),
                           CDecl0 (B,B' as [((Some (CDeclr0 (_,TT',_,_,_)),_),_)],_)],s), _, _)] 
       = #params S'


val [((Some (CDeclr0 (_,s,_,_,_)),_),_)] = A'
val [((Some (CDeclr0 (_,t,_,_,_)),_),_)] = B'

end
\<close>

ML\<open>(#ret o #3 o the)(lookup_Cid_info env_expr "f" );\<close>

ML\<open>
C11_TypeSpec_2_CleanTyp.conv_CDerivedDecl_typ;C_Ast.CFunDeclr0;
val S = hd ((#params o  #3 o the)(lookup_Cid_info env_expr "f" ));
val S' = C11_TypeSpec_2_CleanTyp.conv_CDerivedDecl_typ [S] sigma_i
\<close>
(* and the whole thing a bit more abstract with "a" and "f" *)
ML\<open>
map_option (C11_TypeSpec_2_CleanTyp.conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "a" );
(* map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "f" ); *)
map_option (C11_TypeSpec_2_CleanTyp.conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "x" );
map_option (C11_TypeSpec_2_CleanTyp.conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "y" );
\<close>

end