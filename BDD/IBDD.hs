{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  IBDD(Nat(..), integer_of_nat, equal_nat, Typerepa(..), Itself(..),
        typerep_nat, Typerep(..), Countable(..), Heapa(..), zero_nat, Zero(..),
        default_nat, Default(..), less_eq_nat, Ord(..), less_nat, Preorder(..),
        Order(..), max, nat_of_integer, Num(..), def_hashmap_size_nat,
        Hashable(..), Int(..), int_of_nat, integer_of_int, uint32_of_int,
        hashcode_nat, Linorder(..), Set(..), membera, member, less_eq_set,
        equal_set, typerep_list, Char(..), equal_char, typerep_prod,
        default_prod, plus_nat, def_hashmap_size_prod, hashcode_prod,
        Linorder_list(..), equal_linorder_list, less_eq_linorder_list_pre,
        less_eq_linorder_list, less_linorder_list, IFEXD(..), Hashtable(..),
        Pointermap_impl_ext(..), Bddi_ext(..), one_nat, suc, minus_nat, nth,
        upt, len, new, ntha, upd, const, image, entriesi, arl_nth, pm_pthi,
        dpmi, destrci, remdups, serializeci, apsnd, divmod_integer,
        modulo_integer, modulo_nat, divide_integer, divide_nat, bit_cut_integer,
        char_of_integer, char_of_nat, string_of_nat, graphifyci1, map_filter,
        the_thing_By, the_thing, labelci, mapM, fstp, trd, foldr, graphifyci,
        bot_set, removeAll, inserta, insert, sc_threshold_2_3, gen_length,
        size_list, part, sort_key, sorted_list_of_set, linorder_list_unwrap,
        sorted_list_of_list_set, nat_list_from_vertex, nat_list_from_sc,
        getentryi, times_nat, blita, blit, array_grow, arl_append, load_factor,
        the_array, replicate, ht_new_sz, nat_of_uint32, nat_of_hashcode,
        bounded_hashcode_nat, ls_update, the_size, ht_upd, ht_insls, ht_copy,
        ht_rehash, ht_update, ls_lookup, ht_lookup, pointermap_getmki,
        dpmi_update, ifci, tci, fci, litci, dcli_update, case_ifexici,
        restrict_topci, min, lowest_topsci, equal_IFEXD, param_optci, dcli,
        iteci_lu, andci, bdd_from_vertex_list, orci, bdd_from_sc_list,
        initial_capacity, arl_empty, ht_new, pointermap_empty, emptyci, ex_2_3,
        ex_true, ex_false, another_ex, bdd_from_sc, one_another_ex)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Heap;
import qualified Uint32;
import qualified Data_Bits;

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

typerep_nat :: Itself Nat -> Typerepa;
typerep_nat t = Typerep "Nat.nat" [];

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

class Countable a where {
};

class (Countable a, Typerep a) => Heapa a where {
};

instance Countable Nat where {
};

instance Typerep Nat where {
  typerep = typerep_nat;
};

instance Heapa Nat where {
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = zero_nat;
};

default_nat :: Nat;
default_nat = zero_nat;

class Default a where {
  defaulta :: a;
};

instance Default Nat where {
  defaulta = default_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Nat where {
};

instance Order Nat where {
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

data Num = One | Bit0 Num | Bit1 Num;

def_hashmap_size_nat :: Itself Nat -> Nat;
def_hashmap_size_nat = (\ _ -> nat_of_integer (16 :: Integer));

class Hashable a where {
  hashcode :: a -> Uint32.Word32;
  def_hashmap_size :: Itself a -> Nat;
};

newtype Int = Int_of_integer Integer;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

uint32_of_int :: Int -> Uint32.Word32;
uint32_of_int i = (Prelude.fromInteger (integer_of_int i) :: Uint32.Word32);

hashcode_nat :: Nat -> Uint32.Word32;
hashcode_nat n = uint32_of_int (int_of_nat n);

instance Hashable Nat where {
  hashcode = hashcode_nat;
  def_hashmap_size = def_hashmap_size_nat;
};

class (Order a) => Linorder a where {
};

instance Linorder Nat where {
};

data Set a = Set [a] | Coset [a];

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset xs) (Set ys) =
  (if null xs && null ys then False
    else (error :: forall a. String -> (() -> a) -> a)
           "subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV"
           (\ _ -> less_eq_set (Coset xs) (Set ys)));
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

instance (Eq a) => Eq (Set a) where {
  a == b = equal_set a b;
};

typerep_list :: forall a. (Typerep a) => Itself [a] -> Typerepa;
typerep_list t = Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type];

instance (Countable a) => Countable [a] where {
};

instance (Typerep a) => Typerep [a] where {
  typerep = typerep_list;
};

instance (Heapa a) => Heapa [a] where {
};

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2 x3 x4 x5 x6 x7 x8) (Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;

instance Eq Char where {
  a == b = equal_char a b;
};

typerep_prod :: forall a b. (Typerep a, Typerep b) => Itself (a, b) -> Typerepa;
typerep_prod t =
  Typerep "Product_Type.prod"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

instance (Countable a, Countable b) => Countable (a, b) where {
};

instance (Typerep a, Typerep b) => Typerep (a, b) where {
  typerep = typerep_prod;
};

instance (Heapa a, Heapa b) => Heapa (a, b) where {
};

default_prod :: forall a b. (Default a, Default b) => (a, b);
default_prod = (defaulta, defaulta);

instance (Default a, Default b) => Default (a, b) where {
  defaulta = default_prod;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

def_hashmap_size_prod ::
  forall a b. (Hashable a, Hashable b) => Itself (a, b) -> Nat;
def_hashmap_size_prod =
  (\ _ ->
    plus_nat ((def_hashmap_size :: Itself a -> Nat) Type)
      ((def_hashmap_size :: Itself b -> Nat) Type));

hashcode_prod ::
  forall a b. (Hashable a, Hashable b) => (a, b) -> Uint32.Word32;
hashcode_prod x =
  hashcode (fst x) * (Prelude.fromInteger (33 :: Integer) :: Uint32.Word32) +
    hashcode (snd x);

instance (Hashable a, Hashable b) => Hashable (a, b) where {
  hashcode = hashcode_prod;
  def_hashmap_size = def_hashmap_size_prod;
};

newtype Linorder_list a = LinorderList [a];

equal_linorder_list ::
  forall a. (Eq a, Linorder a) => Linorder_list a -> Linorder_list a -> Bool;
equal_linorder_list (LinorderList x) (LinorderList ya) = x == ya;

instance (Eq a, Linorder a) => Eq (Linorder_list a) where {
  a == b = equal_linorder_list a b;
};

less_eq_linorder_list_pre ::
  forall a. (Eq a, Linorder a) => Linorder_list a -> Linorder_list a -> Bool;
less_eq_linorder_list_pre (LinorderList []) (LinorderList []) = True;
less_eq_linorder_list_pre (LinorderList []) (LinorderList (va : vb)) = True;
less_eq_linorder_list_pre (LinorderList (va : vb)) (LinorderList []) = False;
less_eq_linorder_list_pre (LinorderList (a : asa)) (LinorderList (b : bs)) =
  (if a == b then less_eq_linorder_list_pre (LinorderList asa) (LinorderList bs)
    else less a b);

less_eq_linorder_list ::
  forall a. (Eq a, Linorder a) => Linorder_list a -> Linorder_list a -> Bool;
less_eq_linorder_list x y = less_eq_linorder_list_pre x y;

less_linorder_list ::
  forall a. (Eq a, Linorder a) => Linorder_list a -> Linorder_list a -> Bool;
less_linorder_list x y =
  less_eq_linorder_list_pre x y && not (less_eq_linorder_list_pre y x);

instance (Eq a, Linorder a) => Ord (Linorder_list a) where {
  less_eq = less_eq_linorder_list;
  less = less_linorder_list;
};

instance (Eq a, Linorder a) => Preorder (Linorder_list a) where {
};

instance (Eq a, Linorder a) => Order (Linorder_list a) where {
};

instance (Eq a, Linorder a) => Linorder (Linorder_list a) where {
};

data IFEXD a b = TD | FD | IFD a b b;

data Hashtable a b = HashTable (Heap.STArray Heap.RealWorld [(a, b)]) Nat;

data Pointermap_impl_ext a b =
  Pointermap_impl_ext (Heap.STArray Heap.RealWorld a, Nat) (Hashtable a Nat) b;

data Bddi_ext a =
  Bddi_ext (Pointermap_impl_ext (Nat, (Nat, Nat)) ())
    (Hashtable (Nat, (Nat, Nat)) Nat) a;

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

len ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a -> Heap.ST Heap.RealWorld Nat;
len a = do { 
          i <- Heap.lengthArray a;
          return (nat_of_integer i)
         };

new ::
  forall a.
    (Heapa a) => Nat ->
                   a -> Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a);
new = Heap.newArray . integer_of_nat;

ntha ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Nat -> Heap.ST Heap.RealWorld a;
ntha a n = Heap.readArray a (integer_of_nat n);

upd ::
  forall a.
    (Heapa a) => Nat ->
                   a -> Heap.STArray Heap.RealWorld a ->
                          Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld a);
upd i x a = do { 
              _ <- Heap.writeArray a (integer_of_nat i) x;
              return a
             };

const :: forall a b. a -> b -> a;
const x uu = x;

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

entriesi ::
  forall a b. Pointermap_impl_ext a b -> (Heap.STArray Heap.RealWorld a, Nat);
entriesi (Pointermap_impl_ext entriesi getentryi more) = entriesi;

arl_nth ::
  forall a b.
    (Heapa a) => (Heap.STArray Heap.RealWorld a, b) ->
                   Nat -> Heap.ST Heap.RealWorld a;
arl_nth = (\ (a, _) -> ntha a);

pm_pthi ::
  forall a b.
    (Heapa a) => Pointermap_impl_ext a b -> Nat -> Heap.ST Heap.RealWorld a;
pm_pthi m p = arl_nth (entriesi m) p;

dpmi :: forall a. Bddi_ext a -> Pointermap_impl_ext (Nat, (Nat, Nat)) ();
dpmi (Bddi_ext dpmi dcli more) = dpmi;

destrci :: Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (IFEXD Nat Nat);
destrci n bdd =
  (if equal_nat n zero_nat then return FD
    else (if equal_nat (minus_nat n one_nat) zero_nat then return TD
           else do { 
                  (v, (t, e)) <-
                    pm_pthi (dpmi bdd)
                      (minus_nat (minus_nat n one_nat) one_nat);
                  return (IFD v t e)
                 }));

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

serializeci :: Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld [((Nat, Nat), Nat)];
serializeci p s =
  do { 
    a <- destrci p s;
    (case a of {
      TD -> return [];
      FD -> return [];
      IFD _ t e ->
        do { 
          r <- serializeci t s;
          l <- serializeci e s;
          return (remdups ([((p, t), one_nat), ((p, e), zero_nat)] ++ r ++ l))
         };
    })
   };

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

bit_cut_integer :: Integer -> (Integer, Bool);
bit_cut_integer k =
  (if k == (0 :: Integer) then ((0 :: Integer), False)
    else (case divMod (abs k) (abs (2 :: Integer)) of {
           (r, s) ->
             ((if (0 :: Integer) < k then r else negate r - s),
               s == (1 :: Integer));
         }));

char_of_integer :: Integer -> Char;
char_of_integer k =
  (case bit_cut_integer k of {
    (q0, b0) ->
      (case bit_cut_integer q0 of {
        (q1, b1) ->
          (case bit_cut_integer q1 of {
            (q2, b2) ->
              (case bit_cut_integer q2 of {
                (q3, b3) ->
                  (case bit_cut_integer q3 of {
                    (q4, b4) ->
                      (case bit_cut_integer q4 of {
                        (q5, b5) ->
                          (case bit_cut_integer q5 of {
                            (q6, b6) ->
                              let {
                                a = bit_cut_integer q6;
                              } in (case a of {
                                     (_, aa) -> Char b0 b1 b2 b3 b4 b5 b6 aa;
                                   });
                          });
                      });
                  });
              });
          });
      });
  });

char_of_nat :: Nat -> Char;
char_of_nat = char_of_integer . integer_of_nat;

string_of_nat :: Nat -> [Char];
string_of_nat n =
  (if less_nat n (nat_of_integer (10 :: Integer))
    then [char_of_nat (plus_nat (nat_of_integer (48 :: Integer)) n)]
    else string_of_nat (divide_nat n (nat_of_integer (10 :: Integer))) ++
           [char_of_nat
              (plus_nat (nat_of_integer (48 :: Integer))
                (modulo_nat n (nat_of_integer (10 :: Integer))))]);

graphifyci1 ::
  forall a. a -> ((Nat, Nat), Nat) -> Heap.ST Heap.RealWorld [Char];
graphifyci1 bdd a =
  let {
    aa = a;
  } in (case aa of {
         (ab, b) ->
           (case ab of {
             (f, t) ->
               (\ y ->
                 let {
                   c = string_of_nat f ++
                         [Char False False False False False True False False,
                           Char True False True True False True False False,
                           Char False True True True True True False False,
                           Char False False False False False True False
                             False] ++
                           string_of_nat t;
                 } in return
                        (c ++ (if equal_nat y zero_nat
                                then [Char False False False False False True
False False,
                                       Char True True False True True False True
 False,
                                       Char True True False False True True True
 False,
                                       Char False False True False True True
 True False,
                                       Char True False False True True True True
 False,
                                       Char False False True True False True
 True False,
                                       Char True False True False False True
 True False,
                                       Char True False True True True True False
 False,
                                       Char False False True False False True
 True False,
                                       Char True True True True False True True
 False,
                                       Char False False True False True True
 True False,
                                       Char False False True False True True
 True False,
                                       Char True False True False False True
 True False,
                                       Char False False True False False True
 True False,
                                       Char True False True True True False True
 False]
                                else []) ++
                                [Char True True False True True True False
                                   False,
                                  Char False True False True False False False
                                    False]));
           })
             b;
       });

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

the_thing_By ::
  forall a b. (Eq a) => (a -> a -> Bool) -> [(a, b)] -> [(a, [b])];
the_thing_By f l =
  let {
    a = remdups (map fst l);
  } in map (\ e ->
             (e, map_filter
                   (\ x -> (if f e (fst x) then Just (snd x) else Nothing)) l))
         a;

the_thing :: forall a b. (Eq a) => [(a, b)] -> [(a, [b])];
the_thing = the_thing_By (\ a b -> a == b);

labelci ::
  Bddi_ext () -> Nat -> Heap.ST Heap.RealWorld ([Char], ([Char], [Char]));
labelci s n =
  do { 
    d <- destrci n s;
    let { son = string_of_nat n };
    let { label = (case d of {
                    TD -> [Char False False True False True False True False];
                    FD -> [Char False True True False False False True False];
                    IFD v _ _ -> string_of_nat v;
                  })
      };
    return
      (label,
        (son, son ++
                [Char True True False True True False True False,
                  Char False False True True False True True False,
                  Char True False False False False True True False,
                  Char False True False False False True True False,
                  Char True False True False False True True False,
                  Char False False True True False True True False,
                  Char True False True True True True False False] ++
                  label ++
                    [Char True False True True True False True False,
                      Char True True False True True True False False,
                      Char False True False True False False False False]))
   };

mapM ::
  forall a b.
    (a -> Heap.ST Heap.RealWorld b) -> [a] -> Heap.ST Heap.RealWorld [b];
mapM f [] = return [];
mapM f (a : asa) = do { 
                     r <- f a;
                     rs <- mapM f asa;
                     return (r : rs)
                    };

fstp :: forall a b c. (a, (b, c)) -> (a, b);
fstp = apsnd fst;

trd :: forall a b c. (a, (b, c)) -> c;
trd = snd . snd;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

graphifyci :: [Char] -> Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld [Char];
graphifyci name ep bdd =
  do { 
    s <- serializeci ep bdd;
    let { e = map fst s };
    l <- mapM (labelci bdd) (reverse (remdups (map fst e ++ map snd e)));
    let { grp =
      map (\ la ->
            foldr (\ a t ->
                    t ++ a ++ [Char True True False True True True False False])
              (snd la)
              [Char True True False True True True True False,
                Char False True False False True True True False,
                Char True False False False False True True False,
                Char False True True True False True True False,
                Char True True False True False True True False,
                Char True False True True True True False False,
                Char True True False False True True True False,
                Char True False False False False True True False,
                Char True False True True False True True False,
                Char True False True False False True True False,
                Char True True False True True True False False] ++
              [Char True False True True True True True False,
                Char False True False True False False False False])
        (the_thing (map fstp l))
      };
    ea <- mapM (graphifyci1 bdd) s;
    let { emptyhlp =
      (if equal_nat ep zero_nat
        then [Char False True True False False False True False,
               Char True True False True True True False False,
               Char False True False True False False False False]
        else (if equal_nat (minus_nat ep one_nat) zero_nat
               then [Char False False True False True False True False,
                      Char True True False True True True False False,
                      Char False True False True False False False False]
               else []))
      };
    return
      ([Char False False True False False True True False,
         Char True False False True False True True False,
         Char True True True False False True True False,
         Char False True False False True True True False,
         Char True False False False False True True False,
         Char False False False False True True True False,
         Char False False False True False True True False,
         Char False False False False False True False False] ++
        name ++
          [Char False False False False False True False False,
            Char True True False True True True True False,
            Char False True False True False False False False] ++
            concatMap trd l ++
              concat grp ++
                concat ea ++
                  emptyhlp ++ [Char True False True True True True True False])
   };

bot_set :: forall a. Set a;
bot_set = Set [];

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

sc_threshold_2_3 :: Set (Set Nat);
sc_threshold_2_3 =
  insert bot_set
    (insert (insert zero_nat bot_set)
      (insert (insert one_nat bot_set)
        (insert (insert (nat_of_integer (2 :: Integer)) bot_set)
          (insert (insert (nat_of_integer (3 :: Integer)) bot_set)
            (insert (insert zero_nat (insert one_nat bot_set))
              (insert
                (insert zero_nat
                  (insert (nat_of_integer (2 :: Integer)) bot_set))
                (insert
                  (insert zero_nat
                    (insert (nat_of_integer (3 :: Integer)) bot_set))
                  (insert
                    (insert one_nat
                      (insert (nat_of_integer (2 :: Integer)) bot_set))
                    (insert
                      (insert one_nat
                        (insert (nat_of_integer (3 :: Integer)) bot_set))
                      (insert
                        (insert (nat_of_integer (2 :: Integer))
                          (insert (nat_of_integer (3 :: Integer)) bot_set))
                        bot_set))))))))));

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  (case part f pivot xs of {
    (lts, (eqs, gts)) ->
      let {
        xa = f x;
      } in (if less xa pivot then (x : lts, (eqs, gts))
             else (if less pivot xa then (lts, (eqs, x : gts))
                    else (lts, (x : eqs, gts))));
  });
part f pivot [] = ([], ([], []));

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case part f
              (f (nth xs
                   (divide_nat (size_list xs) (nat_of_integer (2 :: Integer)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

sorted_list_of_set :: forall a. (Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (Set xs) = sort_key (\ x -> x) (remdups xs);

linorder_list_unwrap :: forall a. (Linorder a) => Linorder_list a -> [a];
linorder_list_unwrap l = (case l of {
                           LinorderList la -> la;
                         });

sorted_list_of_list_set :: forall a. (Eq a, Linorder a) => Set [a] -> [[a]];
sorted_list_of_list_set l =
  map linorder_list_unwrap (sorted_list_of_set (image LinorderList l));

nat_list_from_vertex :: forall a. (Eq a, Linorder a) => Set a -> [a];
nat_list_from_vertex v = sorted_list_of_set v;

nat_list_from_sc :: forall a. (Eq a, Linorder a) => Set (Set a) -> [[a]];
nat_list_from_sc k = sorted_list_of_list_set (image nat_list_from_vertex k);

getentryi :: forall a b. Pointermap_impl_ext a b -> Hashtable a Nat;
getentryi (Pointermap_impl_ext entriesi getentryi more) = getentryi;

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

blita ::
  forall a.
    Heap.STArray Heap.RealWorld a ->
      Integer ->
        Heap.STArray Heap.RealWorld a ->
          Integer -> Integer -> Heap.ST Heap.RealWorld ();
blita _ _ _ _ _ = error "Array_Blit.blit\'";

blit ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Nat ->
                     Heap.STArray Heap.RealWorld a ->
                       Nat -> Nat -> Heap.ST Heap.RealWorld ();
blit src si dst di len =
  blita src (integer_of_nat si) dst (integer_of_nat di) (integer_of_nat len);

array_grow ::
  forall a.
    (Heapa a) => Heap.STArray Heap.RealWorld a ->
                   Nat ->
                     a -> Heap.ST Heap.RealWorld
                            (Heap.STArray Heap.RealWorld a);
array_grow a s x =
  do { 
    l <- len a;
    (if equal_nat l s then return a else do { 
   aa <- new s x;
   _ <- blit a zero_nat aa zero_nat l;
   return aa
  })
   };

arl_append ::
  forall a.
    (Default a,
      Heapa a) => (Heap.STArray Heap.RealWorld a, Nat) ->
                    a -> Heap.ST Heap.RealWorld
                           (Heap.STArray Heap.RealWorld a, Nat);
arl_append =
  (\ (a, n) x ->
    do { 
      lena <- len a;
      (if less_nat n lena then do { 
                                 aa <- upd n x a;
                                 return (aa, plus_nat n one_nat)
                                }
        else let {
               newcap = times_nat (nat_of_integer (2 :: Integer)) lena;
             } in do { 
                    aa <- array_grow a newcap defaulta;
                    ab <- upd n x aa;
                    return (ab, plus_nat n one_nat)
                   })
     });

load_factor :: Nat;
load_factor = nat_of_integer (75 :: Integer);

the_array :: forall a b. Hashtable a b -> Heap.STArray Heap.RealWorld [(a, b)];
the_array (HashTable a uu) = a;

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

ht_new_sz ::
  forall a b.
    (Hashable a, Heapa a,
      Heapa b) => Nat -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_new_sz n = let {
                l = replicate n [];
              } in do { 
                     a <- Heap.newListArray l;
                     return (HashTable a zero_nat)
                    };

nat_of_uint32 :: Uint32.Word32 -> Nat;
nat_of_uint32 x = nat_of_integer (Prelude.toInteger x);

nat_of_hashcode :: Uint32.Word32 -> Nat;
nat_of_hashcode = nat_of_uint32;

bounded_hashcode_nat :: forall a. (Hashable a) => Nat -> a -> Nat;
bounded_hashcode_nat n x = modulo_nat (nat_of_hashcode (hashcode x)) n;

ls_update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> ([(a, b)], Bool);
ls_update k v [] = ([(k, v)], False);
ls_update k v ((l, w) : ls) =
  (if k == l then ((k, v) : ls, True) else let {
     r = ls_update k v ls;
   } in ((l, w) : fst r, snd r));

the_size :: forall a b. Hashtable a b -> Nat;
the_size (HashTable uu n) = n;

ht_upd ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> b -> Hashtable a b ->
                              Heap.ST Heap.RealWorld (Hashtable a b);
ht_upd k v ht =
  do { 
    m <- len (the_array ht);
    let { i = bounded_hashcode_nat m k };
    l <- ntha (the_array ht) i;
    let { la = ls_update k v l };
    _ <- upd i (fst la) (the_array ht);
    let { n = (if snd la then the_size ht else suc (the_size ht)) };
    return (HashTable (the_array ht) n)
   };

ht_insls ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => [(a, b)] ->
                    Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_insls [] ht = return ht;
ht_insls ((k, v) : l) ht = ht_upd k v ht >>= ht_insls l;

ht_copy ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => Nat ->
                    Hashtable a b ->
                      Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_copy n src dst =
  (if equal_nat n zero_nat then return dst
    else do { 
           l <- ntha (the_array src) (minus_nat n one_nat);
           ht_insls l dst >>= ht_copy (minus_nat n one_nat) src
          });

ht_rehash ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => Hashtable a b -> Heap.ST Heap.RealWorld (Hashtable a b);
ht_rehash ht =
  do { 
    n <- len (the_array ht);
    ht_new_sz (times_nat (nat_of_integer (2 :: Integer)) n) >>= ht_copy n ht
   };

ht_update ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> b -> Hashtable a b ->
                              Heap.ST Heap.RealWorld (Hashtable a b);
ht_update k v ht =
  do { 
    m <- len (the_array ht);
    (if less_eq_nat (times_nat m load_factor)
          (times_nat (the_size ht) (nat_of_integer (100 :: Integer)))
      then ht_rehash ht else return ht) >>=
      ht_upd k v
   };

ls_lookup :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe b;
ls_lookup x [] = Nothing;
ls_lookup x ((k, v) : l) = (if x == k then Just v else ls_lookup x l);

ht_lookup ::
  forall a b.
    (Eq a, Hashable a, Heapa a,
      Heapa b) => a -> Hashtable a b -> Heap.ST Heap.RealWorld (Maybe b);
ht_lookup x ht = do { 
                   m <- len (the_array ht);
                   let { i = bounded_hashcode_nat m x };
                   l <- ntha (the_array ht) i;
                   return (ls_lookup x l)
                  };

pointermap_getmki ::
  forall a.
    (Default a, Eq a, Hashable a,
      Heapa a) => a -> Pointermap_impl_ext a () ->
                         Heap.ST Heap.RealWorld (Nat, Pointermap_impl_ext a ());
pointermap_getmki a m =
  do { 
    b <- ht_lookup a (getentryi m);
    (case b of {
      Nothing -> do { 
                   p <- return (snd (entriesi m));
                   ent <- arl_append (entriesi m) a;
                   lut <- ht_update a p (getentryi m);
                   u <- return (Pointermap_impl_ext ent lut ());
                   return (p, u)
                  };
      Just l -> return (l, m);
    })
   };

dpmi_update ::
  forall a.
    (Pointermap_impl_ext (Nat, (Nat, Nat)) () ->
      Pointermap_impl_ext (Nat, (Nat, Nat)) ()) ->
      Bddi_ext a -> Bddi_ext a;
dpmi_update dpmia (Bddi_ext dpmi dcli more) = Bddi_ext (dpmia dpmi) dcli more;

ifci ::
  forall a.
    Nat -> Nat -> Nat -> Bddi_ext a -> Heap.ST Heap.RealWorld (Nat, Bddi_ext a);
ifci v t e bdd =
  (if equal_nat t e then return (t, bdd)
    else do { 
           (p, u) <- pointermap_getmki (v, (t, e)) (dpmi bdd);
           return (suc (suc p), dpmi_update (const u) bdd)
          });

tci :: Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
tci bdd = return (one_nat, bdd);

fci :: Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
fci bdd = return (zero_nat, bdd);

litci :: Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
litci v bdd = do { 
                (t, bdda) <- tci bdd;
                (a, b) <- fci bdda;
                ifci v t a b
               };

dcli_update ::
  forall a.
    (Hashtable (Nat, (Nat, Nat)) Nat -> Hashtable (Nat, (Nat, Nat)) Nat) ->
      Bddi_ext a -> Bddi_ext a;
dcli_update dclia (Bddi_ext dpmi dcli more) = Bddi_ext dpmi (dclia dcli) more;

case_ifexici ::
  forall a.
    Heap.ST Heap.RealWorld a ->
      Heap.ST Heap.RealWorld a ->
        (Nat -> Nat -> Nat -> Heap.ST Heap.RealWorld a) ->
          Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld a;
case_ifexici fti ffi fii ni bddi = do { 
                                     a <- destrci ni bddi;
                                     (case a of {
                                       TD -> fti;
                                       FD -> ffi;
                                       IFD aa b c -> fii aa b c;
                                     })
                                    };

restrict_topci ::
  Nat -> Nat -> Bool -> Bddi_ext () -> Heap.ST Heap.RealWorld Nat;
restrict_topci p vr vl bdd =
  case_ifexici (return p) (return p)
    (\ v te ee ->
      return (if equal_nat v vr then (if vl then te else ee) else p))
    p bdd;

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

lowest_topsci :: [Nat] -> Bddi_ext () -> Heap.ST Heap.RealWorld (Maybe Nat);
lowest_topsci [] s = return Nothing;
lowest_topsci (e : es) s =
  case_ifexici (lowest_topsci es s) (lowest_topsci es s)
    (\ v _ _ -> do { 
                  a <- lowest_topsci es s;
                  (case a of {
                    Nothing -> return (Just v);
                    Just u -> return (Just (min u v));
                  })
                 })
    e s;

equal_IFEXD :: forall a b. (Eq a, Eq b) => IFEXD a b -> IFEXD a b -> Bool;
equal_IFEXD FD (IFD x31 x32 x33) = False;
equal_IFEXD (IFD x31 x32 x33) FD = False;
equal_IFEXD TD (IFD x31 x32 x33) = False;
equal_IFEXD (IFD x31 x32 x33) TD = False;
equal_IFEXD TD FD = False;
equal_IFEXD FD TD = False;
equal_IFEXD (IFD x31 x32 x33) (IFD y31 y32 y33) =
  x31 == y31 && x32 == y32 && x33 == y33;
equal_IFEXD FD FD = True;
equal_IFEXD TD TD = True;

param_optci ::
  Nat ->
    Nat ->
      Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Maybe Nat, Bddi_ext ());
param_optci i t e bdd =
  do { 
    (tr, bdda) <- tci bdd;
    (fl, bddb) <- fci bdda;
    ida <- destrci i bddb;
    td <- destrci t bddb;
    ed <- destrci e bddb;
    return
      ((if equal_IFEXD ida TD then Just t
         else (if equal_IFEXD ida FD then Just e
                else (if equal_IFEXD td TD && equal_IFEXD ed FD then Just i
                       else (if equal_nat t e then Just t
                              else (if equal_IFEXD ed TD && equal_nat i t
                                     then Just tr
                                     else (if equal_IFEXD td FD && equal_nat i e
    then Just fl else Nothing)))))),
        bddb)
   };

dcli :: forall a. Bddi_ext a -> Hashtable (Nat, (Nat, Nat)) Nat;
dcli (Bddi_ext dpmi dcli more) = dcli;

iteci_lu ::
  Nat -> Nat -> Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
iteci_lu i t e s =
  do { 
    a <- ht_lookup (i, (t, e)) (dcli s);
    (case a of {
      Nothing ->
        do { 
          aa <- param_optci i t e s;
          (case aa of {
            (Nothing, sa) ->
              do { 
                ab <- lowest_topsci [i, t, e] sa;
                (case ab of {
                  Nothing -> error "Cannot happen";
                  Just ac -> do { 
                               ti <- restrict_topci i ac True sa;
                               tt <- restrict_topci t ac True sa;
                               te <- restrict_topci e ac True sa;
                               fi <- restrict_topci i ac False sa;
                               ft <- restrict_topci t ac False sa;
                               fe <- restrict_topci e ac False sa;
                               (tb, sb) <- iteci_lu ti tt te sa;
                               (fb, sc) <- iteci_lu fi ft fe sb;
                               (r, sd) <- ifci ac tb fb sc;
                               cl <- ht_update (i, (t, e)) r (dcli sd);
                               return (r, dcli_update (const cl) sd)
                              };
                })
               };
            (Just b, sa) -> return (b, sa);
          })
         };
      Just b -> return (b, s);
    })
   };

andci :: Nat -> Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
andci e1 e2 s = do { 
                  (a, b) <- fci s;
                  iteci_lu e1 e2 a b
                 };

bdd_from_vertex_list ::
  [Nat] -> [Nat] -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
bdd_from_vertex_list n [] s = tci s;
bdd_from_vertex_list n (f : fs) s =
  do { 
    (fa, sa) <- (if membera n f then tci s else litci f s);
    (fsa, a) <- bdd_from_vertex_list n fs sa;
    andci fsa fa a
   };

orci :: Nat -> Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
orci e1 e2 s = do { 
                 (t, a) <- tci s;
                 iteci_lu e1 t e2 a
                };

bdd_from_sc_list ::
  [Nat] -> [[Nat]] -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
bdd_from_sc_list lUNIV [] s = fci s;
bdd_from_sc_list lUNIV (la : l) s =
  do { 
    (laa, sa) <- bdd_from_vertex_list la lUNIV s;
    (lb, a) <- bdd_from_sc_list lUNIV l sa;
    orci lb laa a
   };

initial_capacity :: Nat;
initial_capacity = nat_of_integer (16 :: Integer);

arl_empty ::
  forall a b.
    (Default a, Heapa a,
      Zero b) => Heap.ST Heap.RealWorld (Heap.STArray Heap.RealWorld a, b);
arl_empty = do { 
              a <- new initial_capacity defaulta;
              return (a, zero)
             };

ht_new ::
  forall a b.
    (Hashable a, Heapa a, Heapa b) => Heap.ST Heap.RealWorld (Hashtable a b);
ht_new = ht_new_sz ((def_hashmap_size :: Itself a -> Nat) Type);

pointermap_empty ::
  forall a.
    (Default a, Hashable a,
      Heapa a) => Heap.ST Heap.RealWorld (Pointermap_impl_ext a ());
pointermap_empty = do { 
                     hm <- ht_new;
                     arl <- arl_empty;
                     return (Pointermap_impl_ext arl hm ())
                    };

emptyci :: Heap.ST Heap.RealWorld (Bddi_ext ());
emptyci = do { 
            ep <- pointermap_empty;
            ehm <- ht_new;
            return (Bddi_ext ep ehm ())
           };

ex_2_3 :: Heap.ST Heap.RealWorld [Char];
ex_2_3 =
  do { 
    s <- emptyci;
    (a, b) <-
      bdd_from_sc_list
        [zero_nat, one_nat, nat_of_integer (2 :: Integer),
          nat_of_integer (3 :: Integer)]
        (nat_list_from_sc sc_threshold_2_3) s;
    graphifyci
      [Char False False True False True True True False,
        Char False False False True False True True False,
        Char False True False False True True True False,
        Char True False True False False True True False,
        Char True True False False True True True False,
        Char False False False True False True True False,
        Char True True True True False True True False,
        Char False False True True False True True False,
        Char False False True False False True True False,
        Char True True True True True False True False,
        Char False False True False True True True False,
        Char True True True False True True True False,
        Char True True True True False True True False,
        Char True True True True True False True False,
        Char False False True False True True True False,
        Char False False False True False True True False,
        Char False True False False True True True False,
        Char True False True False False True True False,
        Char True False True False False True True False]
      a b
   };

ex_true :: Heap.ST Heap.RealWorld [Char];
ex_true =
  do { 
    s <- emptyci;
    (a, b) <-
      bdd_from_sc_list
        [zero_nat, one_nat, nat_of_integer (2 :: Integer),
          nat_of_integer (3 :: Integer)]
        (nat_list_from_sc
          (insert bot_set
            (insert (insert zero_nat bot_set)
              (insert (insert one_nat bot_set)
                (insert (insert (nat_of_integer (2 :: Integer)) bot_set)
                  (insert (insert (nat_of_integer (3 :: Integer)) bot_set)
                    (insert (insert zero_nat (insert one_nat bot_set))
                      (insert
                        (insert zero_nat
                          (insert (nat_of_integer (2 :: Integer)) bot_set))
                        (insert
                          (insert zero_nat
                            (insert (nat_of_integer (3 :: Integer)) bot_set))
                          (insert
                            (insert one_nat
                              (insert (nat_of_integer (2 :: Integer)) bot_set))
                            (insert
                              (insert one_nat
                                (insert (nat_of_integer (3 :: Integer))
                                  bot_set))
                              (insert
                                (insert (nat_of_integer (2 :: Integer))
                                  (insert (nat_of_integer (3 :: Integer))
                                    bot_set))
                                (insert
                                  (insert zero_nat
                                    (insert one_nat
                                      (insert (nat_of_integer (2 :: Integer))
bot_set)))
                                  (insert
                                    (insert zero_nat
                                      (insert one_nat
(insert (nat_of_integer (3 :: Integer)) bot_set)))
                                    (insert
                                      (insert zero_nat
(insert (nat_of_integer (2 :: Integer))
  (insert (nat_of_integer (3 :: Integer)) bot_set)))
                                      (insert
(insert one_nat
  (insert (nat_of_integer (2 :: Integer))
    (insert (nat_of_integer (3 :: Integer)) bot_set)))
(insert
  (insert zero_nat
    (insert one_nat
      (insert (nat_of_integer (2 :: Integer))
        (insert (nat_of_integer (3 :: Integer)) bot_set))))
  bot_set)))))))))))))))))
        s;
    graphifyci
      [Char False False True False True True True False,
        Char False True False False True True True False,
        Char True False True False True True True False,
        Char True False True False False True True False]
      a b
   };

ex_false :: Heap.ST Heap.RealWorld [Char];
ex_false =
  do { 
    s <- emptyci;
    (a, b) <-
      bdd_from_sc_list
        [zero_nat, one_nat, nat_of_integer (2 :: Integer),
          nat_of_integer (3 :: Integer)]
        (nat_list_from_sc bot_set) s;
    graphifyci
      [Char False True True False False True True False,
        Char True False False False False True True False,
        Char False False True True False True True False,
        Char True True False False True True True False,
        Char True False True False False True True False]
      a b
   };

another_ex :: Heap.ST Heap.RealWorld [Char];
another_ex =
  do { 
    s <- emptyci;
    (a, b) <-
      bdd_from_sc_list
        [zero_nat, one_nat, nat_of_integer (2 :: Integer),
          nat_of_integer (3 :: Integer)]
        (nat_list_from_sc
          (insert bot_set
            (insert (insert zero_nat bot_set)
              (insert (insert one_nat bot_set)
                (insert (insert (nat_of_integer (2 :: Integer)) bot_set)
                  (insert (insert (nat_of_integer (3 :: Integer)) bot_set)
                    (insert (insert zero_nat (insert one_nat bot_set))
                      (insert
                        (insert zero_nat
                          (insert (nat_of_integer (2 :: Integer)) bot_set))
                        (insert
                          (insert zero_nat
                            (insert (nat_of_integer (3 :: Integer)) bot_set))
                          (insert
                            (insert one_nat
                              (insert (nat_of_integer (2 :: Integer)) bot_set))
                            (insert
                              (insert one_nat
                                (insert (nat_of_integer (3 :: Integer))
                                  bot_set))
                              (insert
                                (insert (nat_of_integer (2 :: Integer))
                                  (insert (nat_of_integer (3 :: Integer))
                                    bot_set))
                                (insert
                                  (insert zero_nat
                                    (insert one_nat
                                      (insert (nat_of_integer (2 :: Integer))
bot_set)))
                                  (insert
                                    (insert zero_nat
                                      (insert one_nat
(insert (nat_of_integer (3 :: Integer)) bot_set)))
                                    (insert
                                      (insert zero_nat
(insert (nat_of_integer (2 :: Integer))
  (insert (nat_of_integer (3 :: Integer)) bot_set)))
                                      (insert
(insert one_nat
  (insert (nat_of_integer (2 :: Integer))
    (insert (nat_of_integer (3 :: Integer)) bot_set)))
bot_set))))))))))))))))
        s;
    graphifyci
      [Char True False False False False True True False,
        Char False True True True False True True False,
        Char True True True True False True True False,
        Char False False True False True True True False,
        Char False False False True False True True False,
        Char True False True False False True True False,
        Char False True False False True True True False,
        Char True True True True True False True False,
        Char True False True False False True True False,
        Char False False False True True True True False]
      a b
   };

bdd_from_sc ::
  Set (Set Nat) ->
    Nat -> Bddi_ext () -> Heap.ST Heap.RealWorld (Nat, Bddi_ext ());
bdd_from_sc k n =
  bdd_from_sc_list (nat_list_from_vertex (Set (upt zero_nat n)))
    (nat_list_from_sc k);

one_another_ex :: Heap.ST Heap.RealWorld [Char];
one_another_ex =
  do { 
    s <- emptyci;
    (a, b) <-
      bdd_from_sc_list
        [zero_nat, one_nat, nat_of_integer (2 :: Integer),
          nat_of_integer (3 :: Integer)]
        (nat_list_from_sc
          (insert bot_set
            (insert (insert zero_nat bot_set)
              (insert (insert one_nat bot_set)
                (insert (insert (nat_of_integer (2 :: Integer)) bot_set)
                  (insert (insert (nat_of_integer (3 :: Integer)) bot_set)
                    (insert (insert zero_nat (insert one_nat bot_set))
                      (insert
                        (insert zero_nat
                          (insert (nat_of_integer (2 :: Integer)) bot_set))
                        (insert
                          (insert zero_nat
                            (insert (nat_of_integer (3 :: Integer)) bot_set))
                          (insert
                            (insert one_nat
                              (insert (nat_of_integer (2 :: Integer)) bot_set))
                            (insert
                              (insert one_nat
                                (insert (nat_of_integer (3 :: Integer))
                                  bot_set))
                              (insert
                                (insert (nat_of_integer (2 :: Integer))
                                  (insert (nat_of_integer (3 :: Integer))
                                    bot_set))
                                (insert
                                  (insert zero_nat
                                    (insert one_nat
                                      (insert (nat_of_integer (2 :: Integer))
bot_set)))
                                  (insert
                                    (insert zero_nat
                                      (insert one_nat
(insert (nat_of_integer (3 :: Integer)) bot_set)))
                                    (insert
                                      (insert one_nat
(insert (nat_of_integer (2 :: Integer))
  (insert (nat_of_integer (3 :: Integer)) bot_set)))
                                      bot_set)))))))))))))))
        s;
    graphifyci
      [Char True True True True False True True False,
        Char False True True True False True True False,
        Char True False True False False True True False,
        Char True True True True True False True False,
        Char True False False False False True True False,
        Char False True True True False True True False,
        Char True True True True False True True False,
        Char False False True False True True True False,
        Char False False False True False True True False,
        Char True False True False False True True False,
        Char False True False False True True True False,
        Char True True True True True False True False,
        Char True False True False False True True False,
        Char False False False True True True True False]
      a b
   };

}
