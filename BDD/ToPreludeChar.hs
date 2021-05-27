module ToPreludeChar where {

import qualified IBDD;
import Prelude ((*), (+), (.), (++),(==),(&&)); 
import qualified Prelude;
import qualified Data.Char (chr);

{-nibbleToInt :: IBDD.Nibble -> Prelude.Int;
nibbleToInt IBDD.Nibble0 =  0;
nibbleToInt IBDD.Nibble1 =  1;
nibbleToInt IBDD.Nibble2 =  2;
nibbleToInt IBDD.Nibble3 =  3;
nibbleToInt IBDD.Nibble4 =  4;
nibbleToInt IBDD.Nibble5 =  5;
nibbleToInt IBDD.Nibble6 =  6;
nibbleToInt IBDD.Nibble7 =  7;
nibbleToInt IBDD.Nibble8 =  8;
nibbleToInt IBDD.Nibble9 =  9;
nibbleToInt IBDD.NibbleA = 10;
nibbleToInt IBDD.NibbleB = 11;
nibbleToInt IBDD.NibbleC = 12;
nibbleToInt IBDD.NibbleD = 13;
nibbleToInt IBDD.NibbleE = 14;
nibbleToInt IBDD.NibbleF = 15;
-}

{-charToInt :: IBDD.Char -> Prelude.Int;
charToInt (IBDD.Char n1 n2) = nibbleToInt n1 * 16 + nibbleToInt n2;-}


charToInt :: IBDD.Char -> Prelude.Int;
charToInt (IBDD.Char x1 x2 x3 x4 x5 x6 x7 x8) = 128 * Prelude.fromEnum x1 + 64 * Prelude.fromEnum x2 + 32 * Prelude.fromEnum x3 + 16 * Prelude.fromEnum x4 + 8 * Prelude.fromEnum x5 + 4 * Prelude.fromEnum x6 + 2 * Prelude.fromEnum x7 + Prelude.fromEnum x8;

equal_char :: IBDD.Char -> IBDD.Char -> Prelude.Bool;
equal_char (IBDD.Char x1 x2 x3 x4 x5 x6 x7 x8) (IBDD.Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;


charToChar :: IBDD.Char -> Prelude.Char;
charToChar = Data.Char.chr . charToInt;

isToHs = Prelude.map charToChar;


{-instance Prelude.Show (IBDD.Char) => Prelude.Show [IBDD.Char] where {
	show s = "ISB\"" ++ isToHs s ++ "\""
}-}
}

