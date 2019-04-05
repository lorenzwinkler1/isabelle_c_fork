(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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


theory  UML_Library
imports (* Basic Type Operations *)
        "basic_types/UML_Boolean"
        "basic_types/UML_Void"
        "basic_types/UML_Integer"
        "basic_types/UML_Real"
        "basic_types/UML_String"

        (* Collection Type Operations *)
        "collection_types/UML_Pair"
        "collection_types/UML_Bag"
        "collection_types/UML_Set"
        "collection_types/UML_Sequence"
begin

section{* Miscellaneous Stuff*}

subsection{* Definition: asBoolean *}

definition OclAsBoolean\<^sub>I\<^sub>n\<^sub>t  :: "('\<AA>) Integer \<Rightarrow> ('\<AA>) Boolean" ("(_)->oclAsType\<^sub>I\<^sub>n\<^sub>t'(Boolean')")
where     "OclAsBoolean\<^sub>I\<^sub>n\<^sub>t X = (\<lambda>\<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>\<lceil>\<lceil>X \<tau>\<rceil>\<rceil> \<noteq> 0\<rfloor>\<rfloor>
                              else invalid \<tau>)"

interpretation OclAsBoolean\<^sub>I\<^sub>n\<^sub>t : profile_mono\<^sub>d OclAsBoolean\<^sub>I\<^sub>n\<^sub>t "\<lambda>x. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> \<noteq> 0\<rfloor>\<rfloor>"
                                by unfold_locales (auto simp: OclAsBoolean\<^sub>I\<^sub>n\<^sub>t_def bot_option_def)

definition OclAsBoolean\<^sub>R\<^sub>e\<^sub>a\<^sub>l  :: "('\<AA>) Real \<Rightarrow> ('\<AA>) Boolean" ("(_)->oclAsType\<^sub>R\<^sub>e\<^sub>a\<^sub>l'(Boolean')")
where     "OclAsBoolean\<^sub>R\<^sub>e\<^sub>a\<^sub>l X = (\<lambda>\<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>\<lceil>\<lceil>X \<tau>\<rceil>\<rceil> \<noteq> 0\<rfloor>\<rfloor>
                              else invalid \<tau>)"

interpretation OclAsBoolean\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_mono\<^sub>d OclAsBoolean\<^sub>R\<^sub>e\<^sub>a\<^sub>l "\<lambda>x. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> \<noteq> 0\<rfloor>\<rfloor>"
                                 by unfold_locales (auto simp: OclAsBoolean\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def)

subsection{* Definition: asInteger *}

definition OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l  :: "('\<AA>) Real \<Rightarrow> ('\<AA>) Integer" ("(_)->oclAsType\<^sub>R\<^sub>e\<^sub>a\<^sub>l'(Integer')")
where     "OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l X = (\<lambda>\<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>floor \<lceil>\<lceil>X \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                              else invalid \<tau>)"

interpretation OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_mono\<^sub>d OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l "\<lambda>x. \<lfloor>\<lfloor>floor \<lceil>\<lceil>x\<rceil>\<rceil>\<rfloor>\<rfloor>"
                                 by unfold_locales (auto simp: OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def)

subsection{* Definition: asReal *}

definition OclAsReal\<^sub>I\<^sub>n\<^sub>t  :: "('\<AA>) Integer \<Rightarrow> ('\<AA>) Real" ("(_)->oclAsType\<^sub>I\<^sub>n\<^sub>t'(Real')")
where     "OclAsReal\<^sub>I\<^sub>n\<^sub>t X = (\<lambda>\<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>real_of_int \<lceil>\<lceil>X \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                              else invalid \<tau>)"

interpretation OclAsReal\<^sub>I\<^sub>n\<^sub>t : profile_mono\<^sub>d OclAsReal\<^sub>I\<^sub>n\<^sub>t "\<lambda>x. \<lfloor>\<lfloor>real_of_int \<lceil>\<lceil>x\<rceil>\<rceil>\<rfloor>\<rfloor>"
                             by unfold_locales (auto simp: OclAsReal\<^sub>I\<^sub>n\<^sub>t_def bot_option_def)

lemma Integer_subtype_of_Real:
  assumes "\<tau> \<Turnstile> \<delta> X"
  shows   "\<tau> \<Turnstile> X ->oclAsType\<^sub>I\<^sub>n\<^sub>t(Real) ->oclAsType\<^sub>R\<^sub>e\<^sub>a\<^sub>l(Integer) \<triangleq> X"
  apply(insert assms,  simp add: OclAsInteger\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def OclAsReal\<^sub>I\<^sub>n\<^sub>t_def OclValid_def StrongEq_def)
  apply(subst (2 4) cp_defined, simp add: true_def)
  by (metis assms bot_option_def foundation16 null_option_def option.exhaust_sel)

subsection{* Definition: asPair *}

definition OclAsPair\<^sub>S\<^sub>e\<^sub>q   :: "[('\<AA>,'\<alpha>::null)Sequence]\<Rightarrow>('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair" ("(_)->asPair\<^sub>S\<^sub>e\<^sub>q'(')")
where     "OclAsPair\<^sub>S\<^sub>e\<^sub>q S = (if S->size\<^sub>S\<^sub>e\<^sub>q() \<doteq> \<two>
                            then Pair{S->at\<^sub>S\<^sub>e\<^sub>q(\<zero>),S->at\<^sub>S\<^sub>e\<^sub>q(\<one>)}
                            else invalid
                            endif)"

definition OclAsPair\<^sub>S\<^sub>e\<^sub>t   :: "[('\<AA>,'\<alpha>::null)Set]\<Rightarrow>('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair" ("(_)->asPair\<^sub>S\<^sub>e\<^sub>t'(')")
where     "OclAsPair\<^sub>S\<^sub>e\<^sub>t S = (if S->size\<^sub>S\<^sub>e\<^sub>t() \<doteq> \<two>
                            then let v = S->any\<^sub>S\<^sub>e\<^sub>t() in
                                 Pair{v,S->excluding\<^sub>S\<^sub>e\<^sub>t(v)->any\<^sub>S\<^sub>e\<^sub>t()}
                            else invalid
                            endif)"

definition OclAsPair\<^sub>B\<^sub>a\<^sub>g   :: "[('\<AA>,'\<alpha>::null)Bag]\<Rightarrow>('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair" ("(_)->asPair\<^sub>B\<^sub>a\<^sub>g'(')")
where     "OclAsPair\<^sub>B\<^sub>a\<^sub>g S = (if S->size\<^sub>B\<^sub>a\<^sub>g() \<doteq> \<two>
                            then let v = S->any\<^sub>B\<^sub>a\<^sub>g() in
                                 Pair{v,S->excluding\<^sub>B\<^sub>a\<^sub>g(v)->any\<^sub>B\<^sub>a\<^sub>g()}
                            else invalid
                            endif)"

subsection{* Definition: asSet *}

definition OclAsSet\<^sub>S\<^sub>e\<^sub>q   :: "[('\<AA>,'\<alpha>::null)Sequence]\<Rightarrow>('\<AA>,'\<alpha>)Set" ("(_)->asSet\<^sub>S\<^sub>e\<^sub>q'(')")
where     "OclAsSet\<^sub>S\<^sub>e\<^sub>q S = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = Set{} | x ->including\<^sub>S\<^sub>e\<^sub>t(b)))"

definition OclAsSet\<^sub>P\<^sub>a\<^sub>i\<^sub>r   :: "[('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair]\<Rightarrow>('\<AA>,'\<alpha>)Set" ("(_)->asSet\<^sub>P\<^sub>a\<^sub>i\<^sub>r'(')")
where     "OclAsSet\<^sub>P\<^sub>a\<^sub>i\<^sub>r S = Set{S .First(), S .Second()}"

definition OclAsSet\<^sub>B\<^sub>a\<^sub>g   :: "('\<AA>,'\<alpha>::null) Bag\<Rightarrow>('\<AA>,'\<alpha>)Set" ("(_)->asSet\<^sub>B\<^sub>a\<^sub>g'(')")
where     "OclAsSet\<^sub>B\<^sub>a\<^sub>g S =  (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor> Rep_Set_base S \<tau> \<rfloor>\<rfloor>
                                 else if (\<upsilon> S) \<tau> = true \<tau> then null \<tau>
                                                          else invalid \<tau>)"

subsection{* Definition: asSequence *}

definition OclAsSeq\<^sub>S\<^sub>e\<^sub>t   :: "[('\<AA>,'\<alpha>::null)Set]\<Rightarrow>('\<AA>,'\<alpha>)Sequence" ("(_)->asSequence\<^sub>S\<^sub>e\<^sub>t'(')")
where     "OclAsSeq\<^sub>S\<^sub>e\<^sub>t S = (S->iterate\<^sub>S\<^sub>e\<^sub>t(b; x = Sequence{} | x ->including\<^sub>S\<^sub>e\<^sub>q(b)))"

definition OclAsSeq\<^sub>B\<^sub>a\<^sub>g   :: "[('\<AA>,'\<alpha>::null)Bag]\<Rightarrow>('\<AA>,'\<alpha>)Sequence" ("(_)->asSequence\<^sub>B\<^sub>a\<^sub>g'(')")
where     "OclAsSeq\<^sub>B\<^sub>a\<^sub>g S = (S->iterate\<^sub>B\<^sub>a\<^sub>g(b; x = Sequence{} | x ->including\<^sub>S\<^sub>e\<^sub>q(b)))"

definition OclAsSeq\<^sub>P\<^sub>a\<^sub>i\<^sub>r   :: "[('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair]\<Rightarrow>('\<AA>,'\<alpha>)Sequence" ("(_)->asSequence\<^sub>P\<^sub>a\<^sub>i\<^sub>r'(')")
where     "OclAsSeq\<^sub>P\<^sub>a\<^sub>i\<^sub>r S = Sequence{S .First(), S .Second()}"

subsection{* Definition: asBag *}

definition OclAsBag\<^sub>S\<^sub>e\<^sub>q   :: "[('\<AA>,'\<alpha>::null)Sequence]\<Rightarrow>('\<AA>,'\<alpha>)Bag" ("(_)->asBag\<^sub>S\<^sub>e\<^sub>q'(')")
where     "OclAsBag\<^sub>S\<^sub>e\<^sub>q S = (\<lambda>\<tau>. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lambda>s. if list_ex ((=) s) \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then 1 else 0\<rfloor>\<rfloor>)"

definition OclAsBag\<^sub>S\<^sub>e\<^sub>t   :: "[('\<AA>,'\<alpha>::null)Set]\<Rightarrow>('\<AA>,'\<alpha>)Bag" ("(_)->asBag\<^sub>S\<^sub>e\<^sub>t'(')")
where     "OclAsBag\<^sub>S\<^sub>e\<^sub>t S = (\<lambda>\<tau>. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lambda>s. if s \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> then 1 else 0\<rfloor>\<rfloor>)"

lemma assumes "\<tau> \<Turnstile> \<delta> (S ->size\<^sub>S\<^sub>e\<^sub>t())" (* S is finite *)
      shows "OclAsBag\<^sub>S\<^sub>e\<^sub>t S = (S->iterate\<^sub>S\<^sub>e\<^sub>t(b; x = Bag{} | x ->including\<^sub>B\<^sub>a\<^sub>g(b)))"
oops

definition OclAsBag\<^sub>P\<^sub>a\<^sub>i\<^sub>r   :: "[('\<AA>,'\<alpha>::null,'\<alpha>::null) Pair]\<Rightarrow>('\<AA>,'\<alpha>)Bag" ("(_)->asBag\<^sub>P\<^sub>a\<^sub>i\<^sub>r'(')")
where     "OclAsBag\<^sub>P\<^sub>a\<^sub>i\<^sub>r S = Bag{S .First(), S .Second()}"

text_raw{* \isatagafp *}
subsection{* Collection Types *}
lemmas cp_intro'' [intro!,simp,code_unfold] =
       cp_intro'
     (*  cp_intro''\<^sub>P\<^sub>a\<^sub>i\<^sub>r *)
       cp_intro''\<^sub>S\<^sub>e\<^sub>t
       cp_intro''\<^sub>S\<^sub>e\<^sub>q
text_raw{* \endisatagafp *}

subsection{* Test Statements *}

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including\<^sub>S\<^sub>e\<^sub>t(\<one>)->including\<^sub>S\<^sub>e\<^sub>t(\<two>))"
by (rule refl)

text{* Here is an example of a nested collection. *}
lemma semantic_test2:
assumes H:"(Set{\<two>} \<doteq> null) = (false::('\<AA>)Boolean)"
shows   "(\<tau>::('\<AA>)st) \<Turnstile> (Set{Set{\<two>},null}->includes\<^sub>S\<^sub>e\<^sub>t(null))"
by(simp add: OclIncludes_execute\<^sub>S\<^sub>e\<^sub>t H)



lemma short_cut'[simp,code_unfold]: "(\<eight> \<doteq> \<six>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt8_def OclInt6_def
                 true_def false_def invalid_def bot_option_def)
done

lemma short_cut''[simp,code_unfold]: "(\<two> \<doteq> \<one>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done
lemma short_cut'''[simp,code_unfold]: "(\<one> \<doteq> \<two>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done

Assert   "\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t \<two>) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t \<one>) "


text{* Elementary computations on Sets.*}

declare OclSelect_body_def [simp]

Assert "\<not> (\<tau> \<Turnstile> \<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set))"
Assert    "\<tau> \<Turnstile> \<upsilon>(null::('\<AA>,'\<alpha>::null) Set)"
Assert "\<not> (\<tau> \<Turnstile> \<delta>(null::('\<AA>,'\<alpha>::null) Set))"
Assert    "\<tau> \<Turnstile> \<upsilon>(Set{})"
Assert    "\<tau> \<Turnstile> \<upsilon>(Set{Set{\<two>},null})"
Assert    "\<tau> \<Turnstile> \<delta>(Set{Set{\<two>},null})"
Assert    "\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes\<^sub>S\<^sub>e\<^sub>t(\<one>))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>}->includes\<^sub>S\<^sub>e\<^sub>t(\<one>)))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes\<^sub>S\<^sub>e\<^sub>t(null)))"
Assert    "\<tau> \<Turnstile> (Set{\<two>,null}->includes\<^sub>S\<^sub>e\<^sub>t(null))"
Assert    "\<tau> \<Turnstile> (Set{null,\<two>}->includes\<^sub>S\<^sub>e\<^sub>t(null))"

Assert    "\<tau> \<Turnstile> ((Set{})->forAll\<^sub>S\<^sub>e\<^sub>t(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"

Assert    "\<tau> \<Turnstile> ((Set{\<two>,\<one>})->forAll\<^sub>S\<^sub>e\<^sub>t(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"
Assert "\<not> (\<tau> \<Turnstile> ((Set{\<two>,\<one>})->exists\<^sub>S\<^sub>e\<^sub>t(z | z <\<^sub>i\<^sub>n\<^sub>t \<zero> )))"
Assert "\<not> (\<tau> \<Turnstile> (\<delta>(Set{\<two>,null})->forAll\<^sub>S\<^sub>e\<^sub>t(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert "\<not> (\<tau> \<Turnstile> ((Set{\<two>,null})->forAll\<^sub>S\<^sub>e\<^sub>t(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert    "\<tau> \<Turnstile> ((Set{\<two>,null})->exists\<^sub>S\<^sub>e\<^sub>t(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"


Assert "\<not> (\<tau> \<Turnstile> (Set{null::'a Boolean} \<doteq> Set{}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{null::'a Integer} \<doteq> Set{}))"

Assert "\<not> (\<tau> \<Turnstile> (Set{true} \<doteq> Set{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{true,true} \<doteq> Set{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>} \<doteq> Set{\<one>}))"
Assert    "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Set{\<one>,null,\<two>} <> Set{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} \<doteq> Set{Set{null,\<two>}})"
Assert    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} <> Set{Set{null,\<two>},null})"
Assert    "\<tau> \<Turnstile> (Set{null}->select\<^sub>S\<^sub>e\<^sub>t(x | not x) \<doteq> Set{null})"
Assert    "\<tau> \<Turnstile> (Set{null}->reject\<^sub>S\<^sub>e\<^sub>t(x | not x) \<doteq> Set{null})"

lemma     "const (Set{Set{\<two>,null}, invalid})" by(simp add: const_ss)


text{* Elementary computations on Sequences.*}

(*(*TODO*)declare OclSelect_body_def [simp]*)

Assert "\<not> (\<tau> \<Turnstile> \<upsilon>(invalid::('\<AA>,'\<alpha>::null) Sequence))"
Assert    "\<tau> \<Turnstile> \<upsilon>(null::('\<AA>,'\<alpha>::null) Sequence)"
Assert "\<not> (\<tau> \<Turnstile> \<delta>(null::('\<AA>,'\<alpha>::null) Sequence))"
Assert    "\<tau> \<Turnstile> \<upsilon>(Sequence{})"
(*(*TOFIX*)Assert    "\<tau> \<Turnstile> \<upsilon>(Sequence{Sequence{\<two>},null})"
Assert    "\<tau> \<Turnstile> \<delta>(Sequence{Sequence{\<two>},null})"*)
(*(*TODO*)Assert    "\<tau> \<Turnstile> (Sequence{\<two>,\<one>}->includes\<^sub>S\<^sub>e\<^sub>q(\<one>))"
Assert "\<not> (\<tau> \<Turnstile> (Sequence{\<two>}->includes\<^sub>S\<^sub>e\<^sub>q(\<one>)))"
Assert "\<not> (\<tau> \<Turnstile> (Sequence{\<two>,\<one>}->includes\<^sub>S\<^sub>e\<^sub>q(null)))"
Assert    "\<tau> \<Turnstile> (Sequence{\<two>,null}->includes\<^sub>S\<^sub>e\<^sub>q(null))"
Assert    "\<tau> \<Turnstile> (Sequence{null,\<two>}->includes\<^sub>S\<^sub>e\<^sub>q(null))"*)
(*(*TOFIX*)
Assert    "\<tau> \<Turnstile> ((Sequence{})->forAll\<^sub>S\<^sub>e\<^sub>q(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"

Assert    "\<tau> \<Turnstile> ((Sequence{\<two>,\<one>})->forAll\<^sub>S\<^sub>e\<^sub>q(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"
Assert "\<not> (\<tau> \<Turnstile> ((Sequence{\<two>,\<one>})->exists\<^sub>S\<^sub>e\<^sub>q(z | z <\<^sub>i\<^sub>n\<^sub>t \<zero> )))"
Assert "\<not> (\<tau> \<Turnstile> (\<delta>(Sequence{\<two>,null})->forAll\<^sub>S\<^sub>e\<^sub>q(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert "\<not> (\<tau> \<Turnstile> ((Sequence{\<two>,null})->forAll\<^sub>S\<^sub>e\<^sub>q(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert    "\<tau> \<Turnstile> ((Sequence{\<two>,null})->exists\<^sub>S\<^sub>e\<^sub>q(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"


Assert "\<not> (\<tau> \<Turnstile> (Sequence{null::'a Boolean} \<doteq> Sequence{}))"
Assert "\<not> (\<tau> \<Turnstile> (Sequence{null::'a Integer} \<doteq> Sequence{}))"

Assert "\<not> (\<tau> \<Turnstile> (Sequence{true} \<doteq> Sequence{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Sequence{true,true} \<doteq> Sequence{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Sequence{\<two>} \<doteq> Sequence{\<one>}))"
Assert    "\<tau> \<Turnstile> (Sequence{\<two>,null,\<two>} \<doteq> Sequence{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Sequence{\<one>,null,\<two>} <> Sequence{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Sequence{Sequence{\<two>,null}} \<doteq> Sequence{Sequence{null,\<two>}})"
Assert    "\<tau> \<Turnstile> (Sequence{Sequence{\<two>,null}} <> Sequence{Sequence{null,\<two>},null})"
Assert    "\<tau> \<Turnstile> (Sequence{null}->select\<^sub>S\<^sub>e\<^sub>q(x | not x) \<doteq> Sequence{null})"*)
(*(*TODO*)Assert    "\<tau> \<Turnstile> (Sequence{null}->reject\<^sub>S\<^sub>e\<^sub>q(x | not x) \<doteq> Sequence{null})"*)

lemma     "const (Sequence{Sequence{\<two>,null}, invalid})" by(simp add: const_ss)

(*<*)
section{* Experiment with Cartouches *}

subsection{* ... *}

ML {*
  local
    fun mk_char (s, _) accu =
        fold
          (fn c => fn l =>
               Syntax.const @{const_syntax Cons}
             $ (Syntax.const @{const_syntax Char} $ HOLogic.mk_numeral c)
             $ l)
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string [] = Const (@{const_syntax Nil}, @{typ "char list"})
      | mk_string (s :: ss) = mk_char s (mk_string ss);

    fun mk_int [] = raise TERM ("int_tr", [])
      | mk_int S = let val s = implode(map fst S) in
                    case Int.fromString s of
                            NONE => raise TERM (" int_tr", [])
                         |  SOME(i) => HOLogic.mk_number HOLogic.intT i
                   end

    fun mk_number i =
      let
        fun mk 1 = Syntax.const @{const_syntax Num.One}
          | mk i =
              let
                val (q, r) = Integer.div_mod i 2;
                val bit = if r = 0 then @{const_syntax Num.Bit0} else @{const_syntax Num.Bit1};
              in Syntax.const bit $ (mk q) end;
      in
        if i = 0 then Syntax.const @{const_syntax Groups.zero}
        else if i > 0 then Syntax.const @{const_syntax Num.numeral} $ mk i
        else
          Syntax.const @{const_syntax Groups.uminus} $
            (Syntax.const @{const_syntax Num.numeral} $ mk (~ i))
      end;

    fun mk_frac str =
      let
        val {mant = i, exp = n} = Lexicon.read_float str;
        val exp = Syntax.const @{const_syntax Power.power};
        val ten = mk_number 10;
        val exp10 = if n = 1 then ten else exp $ ten $ mk_number n;
      in Syntax.const @{const_syntax divide} $ mk_number i $ exp10 end;

  in
    val POKE = Unsynchronized.ref ([]:term list)
    fun string_tr f content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_string (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;

   fun int_tr f content args =
      let fun err () = raise TERM ("int_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_int (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;

   fun float_tr f [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u $ p] =
                 c $ f (float_tr f [t]) $ u
      | float_tr _ [Const (str, _)] = mk_frac str
      | float_tr _ ts = (POKE:=ts;raise TERM ("float_tr", ts));
 (* in [(@{syntax_const "_Float"}, K float_tr)] end *)

  end;
*}

term "123"

(*
term "\<open>abc\<close>"
term "\<open>123\<close>"
term "\<open>12,24\<close>"
term "\<open>-12.24\<close>"
*)

syntax "_cartouche_oclstring" :: "cartouche_position \<Rightarrow> _"  ("_")

subsection{* ... *}

parse_translation {*
  [( @{syntax_const "_cartouche_oclstring"}
   , let val cartouche_type = Attrib.setup_config_string @{binding cartouche_type} (K "String") in
       fn ctxt =>

           (case Config.get ctxt cartouche_type of
              "String" => (string_tr
                             (fn x => Abs("_",dummyT,
                                    Syntax.const @{const_syntax Some} $
                                       ( Syntax.const @{const_syntax Some} $ x)))
                             (Symbol_Pos.cartouche_content o Symbol_Pos.explode))
            | "Integer" => int_tr
                             (fn x => Abs("_",dummyT,
                                    Syntax.const @{const_syntax Some} $
                                       ( Syntax.const @{const_syntax Some} $ x)))
                             (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
            | "Real" => float_tr (fn x => Abs("_",dummyT,
                                    Syntax.const @{const_syntax Some} $
                                       ( Syntax.const @{const_syntax Some} $ x)))
            | s => error ("Unregistered return type for the cartouche: \"" ^ s ^ "\""))

     end)]
*}


declare [[cartouche_type="Integer"]]
term "\<open>-123\<close>"
declare [[cartouche_type="Real"]]
(*term "\<open>-123.23\<close>"
ML{* (*!POKE
so, the cartouche invocation yields:*)
val it = [Const ("_constrain" , "_") $ Free ("\<open>-123.23\<close>", "_") $ Free ("<markup>", "_")]: term list
*}*)

syntax
  "_ocl_denotation" :: "str_position => string"    ("'_'")

(*>*)
end
