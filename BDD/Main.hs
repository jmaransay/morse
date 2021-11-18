
import Control.Monad (liftM, (=<<))
import Control.Monad.ST (stToIO)
import IBDD (ex_2_3,ex_false,ex_true,another_ex,one_another_ex)
import qualified IBDD;
import qualified Data.Char (chr)

charTo (IBDD.Char x1 x2 x3 x4 x5 x6 x7 x8) = Data.Char.chr . foldr (\a v -> v * 2 + fromEnum a) 0 $ [x1, x2, x3, x4, x5, x6, x7, x8];
main = do
 putStr =<< (liftM (liftM charTo) . stToIO $ ex_false)
 putStr =<< (liftM (liftM charTo) . stToIO $ ex_true)
 putStr =<< (liftM (liftM charTo) . stToIO $ ex_2_3)
 putStr =<< (liftM (liftM charTo) . stToIO $ another_ex)
 putStr =<< (liftM (liftM charTo) . stToIO $ one_another_ex) 
{-return()
main=writeFile "ex_2_3" (liftM (liftM charTo) . ex_2_3)
main=writeFile "ex_2_3" (liftM (liftM charTo) . stToIO $ ex_2_3)-}
