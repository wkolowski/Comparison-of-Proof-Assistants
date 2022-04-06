--#eval "Hello, world!"

--set_option pp.explicit true
set_option pp.universes false
--set_option pp.notation false

#check (fun x => 2 + x)
#print Function.comp

#print funext
#check @congrArg
--#check extfunApp
--#check funSetoid
#print Quotient.sound
#print Quotient.sound.proof_1

--inductive Subtype {α : Type u} (p : α → Prop) where
--  | mk : (x : α) → p x → Subtype p

def main : List String -> IO Unit
| [] => IO.print "Hello WIDE PUTIN!"
| arg :: _ => IO.print s!"Hello {arg}!"