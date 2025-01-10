(*
A theory of IPv4 IPs.

Usually represented as o1.o2.o3.h
(octet 1, octet 2,  octet 3, host)
they are represented here as
%o1/o2/o3/h% due to Isabelle constraints

Below contains the definition of IPv4 addresses,
classes of IPv4 addresses and related theorems.

*)

theory IP imports Main begin

section "IP definition"

(* 
  The predicate to determine whether a list
  of natural numbers forms a valid IPv4 address
*)
abbreviation isIP:: "nat list \<Rightarrow> bool" where
"isIP L \<equiv> (length L = 4 \<and> (\<forall>x. x \<in> (set L) \<longrightarrow> x < 256))"

(* Basic theorems from the IP definition *)
subsection "IP theorems"

theorem ipVals: "(isIP [o1, o2, o3, h]) = (o1 < 256 \<and> (o2 < 256) \<and> (o3 < 256) \<and> (h < 256))"
  by auto

theorem ipLength:
  assumes "isIP L"
  shows "length L = 4"
  using assms by simp

subsection "IP syntax"

(* The universe of IPv4 addresses *)
abbreviation U:: "(nat list) set" where
  "U \<equiv> {x. isIP x}"

(* Set compliment, within the IPv4 universe *)
abbreviation ipcomp:: "(nat list) set \<Rightarrow> (nat list) set" where
  "ipcomp x  \<equiv> U - x"

notation bot ("\<emptyset>") (* shorthand for the empty set *)
no_notation Not  ("~ _" [40] 40) (* remove overload for IP compliment *)
notation ipcomp ("~") (* shorthand for ip compliment *)

(* Special syntax for IPs, fixes number type bug*)
(*
  - o1 = octet 1
  - o2 = octet 2
  - o3 = octet 3
  - h = host
*)

syntax
  "_ip":: "args \<Rightarrow> nat list" ("%(_)%")

translations
  "%o1/o2/o3/h%" == "[o1, o2, o3, h]::(nat list)"

section "IP usage"

subsection "preliminary theorems"

(* The IP universe is a subset of any list
 and its IP compliment.

 No equality here because the list may
contains elements outside the IP universe.*)
theorem u_sub: "U \<subseteq> (I \<union> ~I)"
   by simp

(*
If only IPs are in a list, then the list
and its IP compliment is equal to the IP universe.
*)
theorem u_closure:
  assumes "\<forall>a. (a \<in> I) \<longrightarrow> isIP a"
  shows "I \<union> ~I = U"
  using assms by auto

(* The double compliment of L is L,
assuming L is a subset of the IP universe.*)
theorem double_comp:
  assumes "L \<subseteq> U"
  shows "~ (~ L) = L"
  using assms by auto

(* A demonstration of IP theory, using real
IPs. IP classes are not used here. *)
subsection "numerical demonstration"

(* The list of accepted IPs *)
abbreviation acceptedIPs where
  "acceptedIPs \<equiv> {
    %100/243/176/82%,
    %98/42/19/90%,
    %195/34/128/199%
  }"

(* The list of rejected IPs (i.e. every unaccepted IP) *)
abbreviation rejectedIPs where
  "rejectedIPs \<equiv> ~acceptedIPs"

(* Show every IP in the accepted list is a legitamate IP*)
theorem accepted_valid: "acceptedIPs \<subseteq> U"
  by simp

(* Proof that a sample IP that is not in the accepted list
will be rejected *)

(* Define that sample IP *)
abbreviation testIP:: "nat list" where
  "testIP \<equiv> %1/2/3/4%"

(* Prove it *)
theorem "testIP \<in> rejectedIPs"
  by simp

section "Local and Outside IPs"

section "IP classes"

(* 
Get the nth element in a list
Per Isabelle convention, the first element
has the index of 1, not 0.
As lists in Isabelle are built from right to left,
elem [a, b] 1 = b and elem [a, b] 2 = a
*)
fun elem:: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"elem [] n = undefined" |
"elem (x # xs) n = 
  (if (Suc (length xs)) = n 
  then x else (elem xs n))"

(* 
Define IP classes per constraints supplied by Microsoft Learn
(see https://learn.microsoft.com/en-us/troubleshoot/windows-client/networking/tcpip-addressing-and-subnetting).
*)

abbreviation classA::"nat list \<Rightarrow> bool" where
"classA L \<equiv> (isIP L \<and> elem L 1 \<noteq> 0 \<and> elem L 1 \<noteq> 255 \<and> elem L 4 > 0 \<and> elem L 4 < 127)"

abbreviation classB::"nat list \<Rightarrow> bool" where
"classB L \<equiv> (isIP L \<and> elem L 1 \<noteq> 0 \<and> elem L 1 \<noteq> 255 \<and> elem L 4 > 127 \<and> elem L 4 \<le> 191)"

abbreviation classC::"nat list \<Rightarrow> bool" where
"classC L \<equiv> (isIP L \<and> elem L 1 \<noteq> 0 \<and> elem L 1 \<noteq> 255 \<and> elem L 4 \<ge> 192  \<and> elem L 4 \<le> 223)"

(* Verify definitions using examples provided in Microsoft Learn *)
subsection "class definition verifications"

theorem "classA %10/52/36/11%"
  by simp

theorem "classB %172/16/52/63%"
  by simp

theorem "classC %192/168/132/123%"
  by simp

(* IP class theorems*)
subsection "IP class theorems"

(* Every IP class is exclusive *)
theorem classA_excl:
  assumes "classA L"
  shows "\<not>classB L \<and> \<not>classC L"
  using assms by simp

theorem classB_excl:
  assumes "classB L"
  shows "\<not>classA L \<and> \<not>classC L"
  using assms by simp

theorem classC_excl:
  assumes "classC L"
  shows "\<not>classA L \<and> \<not>classB L"
  using assms by simp

(* Local vs Outside IPs*)

subsection "Local and Outside Definitions"

abbreviation isLocal:: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
"isLocal L M \<equiv> (isIP L \<and> isIP M \<and> elem L 4 = elem M 4 \<and> elem L 3 = elem M 3 \<and> elem L 2 = elem M 2)"

abbreviation isOutside:: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
"isOutside L M \<equiv> (isIP L \<and> isIP M \<and> \<not>(elem L 4 = elem M 4 \<and> elem L 3 = elem M 3 \<and> elem L 2 = elem M 2))"

(* A relevant theorem and some examples *)

subsection "A Local/Outside theorem"
(* Show an IP is either local or exclusive*)
theorem loc_out_exc:
  assumes
    "isIP L" and
    "isIP M"
  shows
    "isLocal L M \<noteq> isOutside L M"
  using assms by auto

subsection "Numerical examples"

theorem "isLocal %1/2/3/0% %1/2/3/47%"
  by simp

theorem "\<not>isOutside %1/2/3/0% %1/2/3/47%"
  by simp

theorem "isOutside %1/2/3/0% %4/2/3/6%"
  by simp

theorem "\<not>isLocal %1/2/3/0% %4/2/3/6%"
  by simp

end
  
  