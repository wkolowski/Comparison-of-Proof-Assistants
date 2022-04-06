import Syntax.PreorderReasoning
import Data.Nat








-- sak' : (x,y,z : Nat) -> x + (y + z) = y + (x + z)
-- sak' 0 y z = Refl
-- sak' (S k) y z = Calc $
--   |~ 1 + (k + (y + z))
--   ~~ 1 + (k + y) + z ...(cong S $ plusAssociative _ _ _)
--   ~~ 1 + (y + k) + z ...(cong (\x => 1 + x + z) ?h)
--   ~~ ((1 + y) + k) + z ...(?h1)
--   ~~ y + (1 + (k + z)) ...(?h2)
