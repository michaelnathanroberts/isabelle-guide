(*
A theory of ports.

Ports are represented by the IANA using
natural numbers between 0 and 2^16-1.
Such representation is used here too.
*)

theory Port imports Main begin

section "Definition of Ports"

(* The predicate to define ports *)

abbreviation isPort:: "nat \<Rightarrow> bool" where
  "isPort n \<equiv> (n < (2^16))"

section "Port classes"

(* 
Types of ports per the IANA.
See https://www.iana.org/assignments/service-names-port-numbers/service-names-port-numbers.xml
*)

(* System ports *)
abbreviation isSys:: "nat \<Rightarrow> bool" where
"isSys n \<equiv> n < 2^10"

(* User ports *)
abbreviation isUser:: "nat \<Rightarrow> bool" where
"isUser n \<equiv> n \<ge> 2^10 \<and> n < (2^15 + 2^14)"

(* Dynamic, or private, ports*)
abbreviation isDyn :: "nat \<Rightarrow> bool" where
"isDyn n \<equiv> n \<ge> (2^15 + 2^14) \<and> n < 2^16"

section "Port theorems"

(* All types are non-overlaping*)

theorem sys_excl:
  assumes "isSys n"
  shows "\<not>isUser n \<and> \<not>isDyn n"
  using assms by simp

theorem user_excl:
  assumes "isUser n"
  shows "\<not>isSys n \<and> \<not>isDyn n"
  using assms by simp

theorem dyn_excl:
  assumes "isDyn n"
  shows "\<not>isSys n \<and> \<not>isUser n"
  using assms by simp

(* A member of a port classification
is a port *)

theorem sys_port:
  assumes "isSys n"
  shows "isPort n"
  using assms by simp

theorem user_port:
  assumes "isUser n"
  shows "isPort n"
  using assms by simp

theorem dyn_port:
  assumes "isDyn n"
  shows "isPort n"
  using assms by simp

(* Every port can be classified into
the three classifications defined above *)
theorem port_class:
  assumes "isPort n"
  shows "isSys n \<or> isUser n \<or> isDyn n"
  using assms by auto

section "Numerical demonstration"

theorem "isSys 109"
  by simp

theorem "isUser 2000"
  by simp

theorem "isDyn 50000"
  by simp

theorem "\<not>isPort 100000"
  by simp

end