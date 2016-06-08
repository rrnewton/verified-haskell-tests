
theory Scratch

imports Main

begin 

datatype AndState = Bot | TrueBot | BotTrue | TrueTrue | F

fun join :: "AndState \<Rightarrow> AndState \<Rightarrow> AndState" where
  "join TrueBot BotTrue = TrueTrue" |
  "join TrueTrue TrueBot = TrueTrue" |
  "join TrueTrue BotTrue = TrueTrue" |
  "join Bot x = x" |
  "join F _ = F" |
  "join TrueBot TrueBot = TrueBot" |
  "join BotTrue BotTrue = BotTrue" |
  "join TrueTrue TrueTrue = TrueTrue" |
  "join BotTrue TrueBot = TrueTrue" |
  "join TrueBot TrueTrue = TrueTrue" |
  "join BotTrue TrueTrue = TrueTrue" |
  "join x Bot = x" | 
  "join _ F = F" 

lemma join_commutative: "join A B = join B A"
  apply (case_tac A) apply (case_tac B, auto)+
  done

end


(*  "join a b = join b a" *)

