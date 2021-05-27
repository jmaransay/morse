
import ToPreludeChar (isToHs,charToChar,charToInt)
import Control.Monad (liftM)
import Control.Monad.ST (stToIO)
import IBDD (Char,ex_2_3)

main :: IO ()
main = do
 g <- liftM isToHs . stToIO $ ex_2_3
 putStr g
 return ()
