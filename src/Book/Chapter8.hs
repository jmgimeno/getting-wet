{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Book.Chapter8 where

import Data.Set hiding (insert, partition, filter, split, elems, disjoint)
import Prelude  hiding (elem, reverse, filter)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ predicate In X Xs      = Set_mem X Xs            @-}
{-@ predicate Subset X Y   = Set_sub X Y             @-}
{-@ predicate Empty  X     = Set_emp X               @-}
{-@ predicate Inter X Y Z  = X = Set_cap Y Z         @-}
{-@ predicate Union X Y Z  = X = Set_cup Y Z         @-}
{-@ predicate Union1 X Y Z = Union X (Set_sng Y) Z   @-}
{-@ predicate Disjoint X Y = Inter (Set_empty 0) X Y @-}

type List a = [a]

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

{-@ implies :: p:Bool -> q:Bool -> Implies p q  @-}
implies False _    = True
implies _     True = True
implies _    _     = False

{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x = (x == 1 + 1) `implies` (x == 2)

-- Exercise 8.1

{-@ prop_x_y_200 :: _ -> _ -> True @-}
prop_x_y_200 x y = ((x < 100) && (y < 100))
                    `implies` (x + y < 200)

--

{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y
  = (x `intersection` y) == (y `intersection` x)

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = x `union` (y `union` z) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z
  =  x `intersection` (y `union` z)
     ==
     (x `intersection` y) `union` (x `intersection` z)

-- Exercise 8.2

-- It fails if elements of x are in y (because then the difference
-- removes them) => We need x and y to be disjoint.

{-@ fail prop_cup_dif_bad @-}
{-@ prop_cup_dif_bad :: _ -> _ -> True @-}
prop_cup_dif_bad x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = True  -- Fix this with a non-trivial precondition

{-@ prop_cup_dif_bad' :: _ -> _ -> True @-}
prop_cup_dif_bad' x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = (x `intersection` y == empty)

--

{-@ measure elts @-}
elts :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

-- A list with elements S
{-@ type ListS a S = {v:[a] | elts v == S} @-}
-- An empty list
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
-- A list whose contents equal those of list X
{-@ type ListEq a X = ListS a {elts X}    @-}
-- A list whose contents are a subset of list X
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
-- A list whose contents are the union of lists X and Y
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
-- A list whose contents are exactly X and the contents of Y
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{- these measures strengthen the data constructors for lists

data [a] where
  [] :: ListEmp a
  (:) :: x:a -> xs:[a] -> ListUn1 a x xs
  
  -}

{-@ append' :: xs:_ -> ys:_ -> ListUn a xs ys @-}
append' [] ys     = ys
append' (x:xs) ys = x : append' xs ys

-- Exercise 8.3

{-@ reverse' :: xs:_ -> ListEq a xs @-}
reverse' xs = revHelper [] xs

{-@ revHelper :: acc:_ -> xs:_ -> ListUn a acc xs @-}
revHelper acc [] = acc
revHelper acc (x:xs) = revHelper (x:acc) xs

-- Exercise 8.4

{-@ halve :: _ -> xs:_ -> {ys:_ | elts xs == Set_cup (elts (fst ys)) (elts (snd ys))} @-}
halve :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

{-@ prop_halve_append :: _ -> _ -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs'      = append' ys zs
    (ys, zs) = halve n xs

-- Exercise 8.5

{-@ elem :: (Eq a) => x:_ -> ys:_ -> {v:Bool | v <=> Set_sub (singleton x) (elts ys) } @-}
elem _ [] = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1 = elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2 = elem 2 [1, 3]

--

{-@ insert :: (Ord a) => x:a -> xs:[a] -> ListUn1 a x xs @-}
insert x [] = [x]
insert x (y:ys)
  | x <= y    = x : y : ys
  | otherwise = y : insert x ys

{-@ insertSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

-- Exercise 8.6

{-@ merge :: xs:[a] -> ys:[a] -> ListUn a xs ys @-}
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y    = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

{-@ prop_merge_app :: _ -> _ -> True @-}
prop_merge_app xs ys = elts zs == elts zs'
  where
    zs  = append' xs ys
    zs' = merge xs ys

-- Exercise 8.7

{-@ mergeSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
mergeSort :: (Ord a) => [a] -> [a]
mergeSort [] = []
mergeSort xs = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs) = halve mid xs
    mid      = length xs `div` 2

--

{-@ measure unique @-}
unique :: (Ord a) => [a] -> Bool
unique []     = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:[a] | unique v } @-}

{-@ isUnique :: UList Integer @-}
isUnique = [1, 2, 3]

{-@ fail isNotUnique @-}
{-@ isNotUnique :: UList Integer @-}
isNotUnique = [1, 2, 3, 1]

{-@ filter :: (a -> Bool)
           -> xs:UList a
           -> {v:ListSub a xs | unique v}
  @-}
filter _ [] = []
filter f (x:xs)
  | f x       = x : xs'
  | otherwise = xs'
  where
    xs' = filter f xs

-- Exercise 8.8

{-@ filter' :: (a -> Bool)
            -> xs:[a]
            -> {v:ListSub a xs | unique xs => unique v}
  @-}
filter' _ [] = []
filter' f (x:xs)
  | f x     = x : xs'
  | otherwise = xs'
  where
    xs' = filter f xs'

{-@ test3 :: UList _ @-}
test3 = filter' (> 2) [1, 2, 3, 4]

{-@ test4 :: [_] @-}
test4 = filter' (> 3) [3, 1, 2, 3]

-- Exercise 8.9

{-@ reverse :: xs:UList a 
            -> {ys:UList a | (elts xs) == (elts ys)} @-}
reverse :: [a] -> [a]
reverse = go []
   where
    {-@ go :: acc:UList a 
           -> {xs:UList a | Disjoint (elts acc) (elts xs)} 
           -> {ys:UList a | Union (elts ys) (elts acc) (elts xs)} @-}
    go acc [] = acc
    go acc (x:xs) = go (x:acc) xs

--

{-@ nub :: [a] -> UList a @-}
nub xs = go [] xs
  where
    {-@ go :: UList a -> xs:[a] -> UList a / [len xs] @-}
    go seen [] = seen
    go seen (x:xs)
      | x `isin` seen = go seen xs
      | otherwise     = go (x : seen) xs

-- FIXME ??? (it seems to work w/o fixing anything)
{-@ predicate In X Xs = Set_mem X (elts Xs) @-}

{-@ isin :: x:_ -> ys:_ -> {v:Bool | v <=> In x ys } @-}
isin x (y:ys)
  | x == y    = True
  | otherwise = x `isin` ys
isin _ [] = False

-- Exercise 8.10

-- Because they can share common elements making the result of appending a list
-- with duplicates

{-@ append :: xs:UList a 
           -> {ys:UList a | Disjoint (elts xs) (elts ys)} 
           -> {zs:UList a | Union (elts zs) (elts xs) (elts ys) } @-}
append [] ys     = ys
append (x:xs) ys = x : append xs ys

-- Exercise 8.11

{-@ type Btwn I J = {v:_ | I <= v && v < J} @-}

{-@ ignore range @-}
{-@ range :: i:Int -> j:Int -> UList (Btwn i j) @-}
range :: Int -> Int -> [Int]
range i j
  | i < j     = add i (range (i + 1) j)
  | otherwise = []
  where
    {-@ add :: x:_
            -> {xs:UList _ | not (In x xs)}
            -> {ys:UList _ | Union1 (elts ys) x (elts xs)} @-}
    add x xs = x : xs 
    
--

data Zipper a = Zipper {
    focus :: a
  , left  :: [a]
  , right :: [a] 
}

{-@ data Zipper a = Zipper {
      focus :: a
    , left  :: {v:UList a | not (In focus v)}
    , right :: {v:UList a | not (In focus v) && Disj v left}
    } @-}

{-@ predicate Disj X Y = Disjoint (elts X) (elts Y) @-}

{-@ differentiate :: UList a -> Maybe (Zipper a) @-}
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs

-- Exercise 8.12

-- NOTE: Strengthen types of reverse and append

{-@ integrate :: Zipper a -> UList a @-}
integrate (Zipper x l r) = reverse l `append` (x : r)

--

focusLeft :: Zipper a -> Zipper a
focusLeft (Zipper t (l:ls) rs) = Zipper l ls (t:rs)
focusLeft (Zipper t [] rs)     = Zipper x xs []
  where
    (x:xs) = reverse (t:rs)

focusRight :: Zipper a -> Zipper a
focusRight = reverseZipper . focusLeft . reverseZipper

reverseZipper :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls

filterZipper :: (a -> Bool) -> Zipper a -> Maybe (Zipper a)
filterZipper p (Zipper f ls rs)
  = case filter p (f:rs) of
      f':rs' -> Just $ Zipper f' (filter p ls) rs'
      []     -> case filter p ls of
                  f':ls' -> Just $ Zipper f' ls' []
                  []     -> Nothing
