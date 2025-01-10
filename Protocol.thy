(*
A theory of protocols.

The Internet Assigned Numbers Authority (IANA)
uses natural numbers \<le> 255 to represent protocols.
So does this theory.
*)

theory Protocol imports Main begin

section "Protocol definition"

(* Predicate that defines protocols *)

abbreviation isProtocol:: "nat \<Rightarrow> bool" where
  "isProtocol n \<equiv> (n \<le> 255)"

(* 
Types of protocols. 
This is per the Internet Assigned Numbers Authority (IANA).
See https://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml
 *)
section "Protocol types"

abbreviation isAssigned::"nat \<Rightarrow> bool" where
"isAssigned n \<equiv> n < 146 \<or> n > 252 \<and> n \<le> 255"

abbreviation isUnassigned::"nat \<Rightarrow> bool" where
"isUnassigned n \<equiv> n \<ge> 146 \<and> n \<le> 252"

abbreviation isExperimental:: "nat \<Rightarrow> bool" where
"isExperimental n \<equiv> n = 253 \<or> n = 254"

abbreviation isReserved:: "nat \<Rightarrow> bool" where
"isReserved n \<equiv> n = 255"


(* Some theorems *)
section "Theorems for protocol types"

theorem exclusive_assignment:
  assumes "isProtocol n"
  shows "isAssigned n \<noteq> isUnassigned n"
  using assms by auto

theorem assigned_protocol:
  assumes "isAssigned n"
  shows "isProtocol n"
  using assms by auto

theorem unassigned_protocol:
  assumes "isUnassigned n"
  shows "isProtocol n"
  using assms by simp

theorem experimental_assigned:
  assumes "isExperimental n"
  shows "isAssigned n"
  using assms by auto

theorem reserved_assigned:
  assumes "isReserved n"
  shows "isAssigned n"
  using assms by simp

theorem experimental_protocol:
  assumes "isExperimental n"
  shows "isProtocol n"
  using assms by auto

theorem reserved_protocol:
  assumes "isReserved n"
  shows "isProtocol n"
  using assms by simp


(* Numerical examples *)
section "Numerical demonstration"

theorem "isProtocol 5"
  by simp

theorem "\<not>isProtocol 257"
  by simp

theorem "isAssigned 24"
  by simp

theorem "isUnassigned 200"
  by simp

theorem "\<not>isAssigned 200"
  by simp

theorem "\<not>isUnassigned 24"
  by simp

theorem "isExperimental 253"
  by simp

theorem "\<not>isExperimental 43"
  by simp

theorem "isReserved 255"
  by simp

theorem "\<not>isReserved 3"
  by simp

end
