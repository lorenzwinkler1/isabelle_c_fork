theory Employee_DesignModel_UMLPart_generated imports "../src/OCL_main" begin

(* 1 *********************************** *)
datatype type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid "nat option" "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "int option" "oid option"
datatype type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t oid "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "nat option"
datatype type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y oid
datatype typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "unit option" "bool option"
datatype type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid
datatype typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 2 *********************************** *)
datatype \<AA> = in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 3 *********************************** *)
type_synonym Boolean = "\<AA> Boolean"
type_synonym Person = "(\<AA>, typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) val"
type_synonym Planet = "(\<AA>, typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option) val"
type_synonym Galaxy = "(\<AA>, typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option option) val"
type_synonym OclAny = "(\<AA>, typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) val"

(* 4 *********************************** *)
instantiation typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n t _ _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (_) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t t _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (_) (_)) \<Rightarrow> t
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y t _ _ \<Rightarrow> (case t of (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 5 *********************************** *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n Person \<Rightarrow> oid_of Person
    | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t Planet \<Rightarrow> oid_of Planet
    | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y Galaxy \<Rightarrow> oid_of Galaxy
    | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 6 *********************************** *)
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "(x::Person) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "(x::Planet) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "(x::Galaxy) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"

(* 7 *********************************** *)
consts OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Planet" ("(_) .oclAsType'(Planet')")
consts OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Galaxy" ("(_) .oclAsType'(Galaxy')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 8 *********************************** *)
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclAsType(Person) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclAsType(Planet) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(Galaxy) \<equiv> x"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor>))"

(* 9 *********************************** *)
definition "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)))))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)))))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_)))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = \<lfloor>\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>"

(* 10 *********************************** *)
lemmas [simp] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 11 *********************************** *)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)

(* 12 *********************************** *)
lemmas [simp] = cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 13 *********************************** *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Galaxy)) = invalid"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclAsType(Galaxy)) = null"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclAsType(Planet)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclAsType(Planet)) = null"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclAsType(Person)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclAsType(Person)) = null"
by(simp)

(* 14 *********************************** *)
lemmas [simp] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 15 *********************************** *)
consts OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Planet')")
consts OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Galaxy')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 16 *********************************** *)
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 17 *********************************** *)
definition "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Person)))"
definition "OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Planet)))"
definition "OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Galaxy))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Galaxy)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(OclAny)))"

(* 18 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 19 *********************************** *)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)

(* 20 *********************************** *)
lemmas [simp] = cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 21 *********************************** *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 22 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 23 *********************************** *)
consts OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Planet')")
consts OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Galaxy')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 24 *********************************** *)
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"

(* 25 *********************************** *)
definition "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Person)))"
definition "OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Planet)))"
definition "OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Galaxy))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Galaxy)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(OclAny)))"

(* 26 *********************************** *)
lemmas [simp] = OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 27 *********************************** *)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)

(* 28 *********************************** *)
lemmas [simp] = cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 29 *********************************** *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null, simp)

(* 30 *********************************** *)
lemmas [simp] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 31 *********************************** *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = id"

(* 32 *********************************** *)
definition "deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 33 *********************************** *)
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>salary\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (salary)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>boss\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (boss)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>weight\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<lfloor>sound\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<lfloor>moving\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"

(* 34 *********************************** *)
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>weight\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>sound\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<lfloor>moving\<rfloor>))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>sound\<rfloor>) (_))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (f) (Person)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>moving\<rfloor>))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (f) (Person)))"

(* 35 *********************************** *)
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> ("(1(_) .salary)" 50)
  where "(x) .salary = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ("(1(_) .boss)" 50)
  where "(x) .boss = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state))))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre ("(1(_) .salary@pre)" 50)
  where "(x) .salary@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre ("(1(_) .boss@pre)" 50)
  where "(x) .boss@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state))))))))"
definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> ("(1(_) .weight)" 50)
  where "(x) .weight = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre ("(1(_) .weight@pre)" 50)
  where "(x) .weight@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> ("(1(_) .sound)" 50)
  where "(x) .sound = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> ("(1(_) .moving)" 50)
  where "(x) .moving = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre ("(1(_) .sound@pre)" 50)
  where "(x) .sound@pre = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre ("(1(_) .moving@pre)" 50)
  where "(x) .moving@pre = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"

(* 36 *********************************** *)
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"

end
