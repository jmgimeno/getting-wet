{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Book.Chapter5 
    ( Sparse(..)
    , okSP, badSP, test1, test2
    , fromList
    , IncList(..)
    , okList, badList
    , insertSort, insertSort', mergeSort, quickSort
    , BST (..)
    , mem, add, delMin, del, bstSort, toBST, toIncList
    ) where

import Data.List (foldl', sort)
import Data.Maybe (fromJust)
import Data.Vector hiding (foldl', foldr, fromList, (++))

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
    deriving Show

{-@ type Nat = {v:Int | 0 <= v}                   @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ data Sparse a = SP { spDim :: Nat
                       , spElems :: [(Btwn 0 spDim, a)] } @-}

{- generated internal representation

data Sparse a where
    SP :: spDim: Nat
       -> spElems:[(Btwn 0 spDim, a)]
       -> Sparse a 
-}

okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]

{-@ fail badSP @-}
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
    where
        go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
        go sum []            = sum

{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' :: Vector Int -> Sparse Int -> Int
dotProd' x (SP _ y) = foldl' body 0 y
    where
        body sum (i, v) = sum + (x ! i) * v

-- Exercise 5.1

{-@ fromList :: dim:Int -> [(Int, a)] -> Maybe (SparseN a dim) @-}
fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = 
    if (dim < 0) 
        then Nothing 
        else fmap (SP dim) (traverse tr elts)
                where
                    tr (i, v) = if (0 <= i) && (i < dim) 
                                    then Just (i, v) 
                                    else Nothing

{- This should work (I think) but LH refuses
fromList dim elts = do
    guard (dim >= 0)
    elts' <- traverse tr elts
    return $ SP dim elts'
    where tr (i, v) = if (0 <= i) && (i < dim) 
                                    then Just (i, v) 
                                    else Nothing
-}

-- >>> fromList 3 [(0, "cat"), (2, "mouse")]
-- Just (SP {spDim = 3, spElems = [(0,"cat"),(2,"mouse")]})
--

{-@ test1 :: SparseN String 3 @-}
test1 :: Sparse String
test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]

-- Exercise 5.2

{-@ plus :: x:Sparse a -> SparseN a (spDim x) -> SparseN a (spDim x) @-}
plus :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus (SP dim xs) (SP _ ys) = SP dim (merge xs ys)
    where
        merge [] ys = ys
        merge (x:xs') ys = merge xs' (insert x ys)
        insert x [] = [x]
        insert x@(i, v) ((j, w):ys) 
            | i == j = (i, v + w) : ys
            | i /= j = (j, w) : insert x ys

{- supposes ordered spElems
plus (SP dim x) (SP _ y) = SP dim (merge x y)
    where 
        merge [] y = y
        merge x [] = x
        merge x@((i, v):x') y@((j, w):y')
            | i < j  = (i, v) : merge x' y
            | i == j = (i, v + w) : merge x' y'
            | i > j  = (j, w) : merge x y'
-}

{- crude but also works
plus (SP dim x) (SP _ y) = SP dim (x ++ y)
-}

{-@ test2 :: SparseN Int 3 @-}
test2 :: Sparse Int
test2 = plus vec1 vec2
    where
        vec1 = SP 3 [(0, 12), (2, 9)]
        vec2 = SP 3 [(0, 8), (1, 100)]

-- >>> test2
-- SP {spDim = 3, spElems = [(0,20),(1,100),(2,9)]}
--

data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}} @-}

{- geneated internal representation

data IncList a where
    Emp  :: IncList a
    (:<) :: hd:a -> tl:IncList {v:a | hd <= v} -> Inclist a
-}

okList  = 1 :< 2 :< 3 :< Emp

{-@ fail badList @-}
badList = 2 :< 1 :< 3 :< Emp

insertSort :: (Ord a) => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = insert x (insertSort xs)

insert :: (Ord a) => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs)
    | y <= x    = y :< x :< xs
    | otherwise = x :< insert y xs

-- Exercise 5.3

insertSort' :: (Ord a) => [a] -> IncList a
insertSort' = foldr insert Emp

--

split :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
    where
        (xs, ys) = split zs
split xs = (xs, [])

merge :: (Ord a) => IncList a -> IncList a -> IncList a
merge xs Emp = xs
merge Emp ys = ys
merge (x :< xs) (y :< ys)
    | x <= y    = x :< merge xs (y :< ys)
    | otherwise = y :< merge (x :< xs) ys
merge _ _ = Emp -- liquid haskell seems to need it !!!

mergeSort :: (Ord a) => [a] -> IncList a
mergeSort [] = Emp
mergeSort [x] = x :< Emp
mergeSort xs = merge (mergeSort ys) (mergeSort zs)
    where (ys, zs) = split xs

-- Exercise 5.4

quickSort :: (Ord a) => [a] -> IncList a
quickSort [] = Emp
quickSort (x:xs) = append x lessers greaters
    where
        lessers  = quickSort [y | y <- xs, y < x]
        greaters = quickSort [z | z <- xs, z >= x]

{-@ append :: (Ord a) 
           => x:a 
           -> IncList {v:a | v < x} 
           -> IncList {v:a | v >= x}
           -> IncList a @-}
append z Emp       ys = z :< ys
append z (x :< xs) ys = x :< append z xs ys

--

data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }

okBST :: BST Int
okBST =  Node 6
             (Node 2
                 (Node 1 Leaf Leaf)
                 (Node 4 Leaf Leaf))
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)

{-@ data BST a    = Leaf
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}

{-@ type BSTL a X = BST {v:a | v < X}             @-}
{-@ type BSTR a X = BST {v:a | X < v}             @-}

{- generated internal representation !

data BST a where
  Leaf :: BST a
  Node :: r:a 
       -> BST {v:a | v < r}
       -> BST {v:a | r < v}
       -> BST a
-}

{-@ fail badBST @-}
badBST =  Node 66
             (Node 4
                 (Node 1 Leaf Leaf)
                 (Node 69 Leaf Leaf))  -- Out of order, rejected
             (Node 99
                 (Node 77 Leaf Leaf)
                 Leaf)

-- Exercise 5.5

-- The BST defined above cannot have duplicates

--

mem :: (Ord a) => a -> BST a -> Bool
mem _ Leaf = False
mem k (Node k' l r)
    | k == k'   = True
    | k <  k'   = mem k l
    | otherwise = mem k r

one   :: a -> BST a
one x = Node x Leaf Leaf

add :: (Ord a) => a -> BST a -> BST a
add k' Leaf = one k'
add k' t@(Node k l r)
    | k' < k    = Node k (add k' l) r
    | k  < k'   = Node k l (add k' r)
    | otherwise = t

data MinPair a = MP { mElt :: a, rest :: BST a }

{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}

{-@ ignore delMin @-}

delMin :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
    where
        MP k' l' = delMin l
delMin Leaf = die "Don't say I didn't warn ya!"

-- Exercise 5.6

del :: (Ord a) => a -> BST a -> BST a
del k' t@(Node k l r)
    | k' < k    = Node k (del k' l) r
    | k  < k'   = Node k l (del k' r)
    | otherwise = case r of
                      Leaf -> l
                      _    -> Node k'' l r'
                                  where
                                      MP k'' r' = delMin r
del _  Leaf = Leaf

-- Exercise 5.7

-- TODO : How to verify the call to die in delMin

-- Exercise 5.8

bstSort :: (Ord a) => [a] -> IncList a
bstSort = toIncList . toBST

toBST :: (Ord a) => [a] -> BST a
toBST = foldr add Leaf

toIncList :: BST a -> IncList a
toIncList (Node x l r) = append x (toIncList l) (toIncList r)
toIncList Leaf         = Emp
