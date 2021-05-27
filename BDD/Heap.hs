
module Heap(ST, RealWorld, STRef, newSTRef, readSTRef, writeSTRef,
  STArray, newArray, newListArray, newFunArray, lengthArray, readArray, writeArray) where

import Control.Monad(liftM)
import Control.Monad.ST(RealWorld, ST)
import Data.STRef(STRef, newSTRef, readSTRef, writeSTRef)
import qualified Data.Array.ST

type STArray s a = Data.Array.ST.STArray s Integer a

newArray :: Integer -> a -> ST s (STArray s a)
newArray k = Data.Array.ST.newArray (0, k - 1)

newListArray :: [a] -> ST s (STArray s a)
newListArray xs = Data.Array.ST.newListArray (0, (fromInteger . toInteger . length) xs - 1) xs

newFunArray :: Integer -> (Integer -> a) -> ST s (STArray s a)
newFunArray k f = Data.Array.ST.newListArray (0, k - 1) (map f [0..k-1])

lengthArray :: STArray s a -> ST s Integer
lengthArray a = liftM (\(_, l) -> l + 1) (Data.Array.ST.getBounds a)

readArray :: STArray s a -> Integer -> ST s a
readArray = Data.Array.ST.readArray

writeArray :: STArray s a -> Integer -> a -> ST s ()
writeArray = Data.Array.ST.writeArray
