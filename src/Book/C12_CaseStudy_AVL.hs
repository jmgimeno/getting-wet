{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Book.C12_CaseStudy_AVL where

import qualified Data.Set as S
import Prelude hiding (max)

--

{-@ die :: {v:_ | false} -> a @-}
die x = error x

{-@ invariant {v:AVL a | 0 <= realHeight v && realHeight v = getHeight v} @-}

{-@ inv_proof  :: t:AVL a -> {v:_ | 0 <= realHeight t && realHeight t = getHeight t } @-}
inv_proof Leaf           = True
inv_proof (Node k l r n) = inv_proof l && inv_proof r

--

-- Georgy Adelson-Velski
-- Evgenii Landis

data AVL a =
    Leaf
  | Node { key :: a      -- value
         , l   :: AVL a  -- left subtree
         , r   :: AVL a  -- right subtree
         , ah  :: Int    -- height
         }
  deriving (Show)

-- | Trees with value less than X
{-@ type AVLL a X = AVL {v:a | v < X} @-}

-- | Trees with value greater than X
{-@ type AVLR a X = AVL {v:a | X < v} @-}

{-@ measure realHeight @-}
realHeight :: AVL a -> Int
realHeight Leaf           = 0
realHeight (Node _ l r _) = nodeHeight l r

{-@ inline nodeHeight @-}
nodeHeight l r = 1 + max hl hr
  where
    hl = realHeight l
    hr = realHeight r

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ inline isReal @-}
isReal v l r = v == nodeHeight l r

{-@ inline isBal @-}
isBal l r n = 0 - n <= d && d <= n
  where
    d = realHeight l - realHeight r

{-@ data AVL a = 
        Leaf
      | Node { key :: a
             , l   :: AVLL a key
             , r   :: {v:AVLR a key | isBal l v 1}
             , ah  :: {v:Nat | isReal v l r}
             }
  @-}

-- | Trees of height N
{-@ type AVLN a N = {v:AVL a | realHeight v == N} @-}

-- | Trees of height equal to that of another T
{-@ type AVLT a T = AVLN a {realHeight T} @-}

{-@ empty :: AVLN a 0 @-}
empty = Leaf

-- Exercise 12.1

{-@ singleton :: a -> AVLN a 1 @-}
singleton x = Node x empty empty 1

-- Exercise 12.2

{-@ mkNode :: k:a 
           -> l:AVLL a k 
           -> r:{AVLR a k | isBal l r 1}
           -> AVLN a {nodeHeight l r}
  @-}
mkNode v l r = Node v l r h
 where
   h       = 1 + max hl hr
   hl      = getHeight l
   hr      = getHeight r

--

{-@ ignore insert0 @-}
{-@ insert0 :: (Ord a) => a -> AVL a -> AVL a @-}
insert0 y t@(Node x l r _)
  | y < x    = mkNode x (insert0 y l) r
  | x < y    = mkNode x l (insert0 y r)
  | otherwise = t
insert0 y Leaf = singleton y

{-@ inline leftBig @-}
leftBig l r = diff l r == 2

{-@ inline rightBig @-}
rightBig l r = diff r l == 2

{-@ inline diff @-}
diff s t = getHeight s - getHeight t

{-@ measure getHeight @-}
getHeight Leaf           = 0
getHeight (Node _ _ _ n) = n

{-@ measure balFac @-}
balFac Leaf           = 0
balFac (Node _ l r _) = getHeight l - getHeight r

{-@ inline leftHeavy @-}
leftHeavy t = balFac t > 0

{-@ inline rightHeavy @-}
rightHeavy t = balFac t < 0

{-@ inline noHeavy @-}
noHeavy t = balFac t == 0

{-@ balL0 :: x:a
          -> l:{AVLL a x | noHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLN a {realHeight l + 1}
  @-}
balL0 v (Node lv ll lr _) r = mkNode lv ll (mkNode v lr r)

{-@ balLL :: x:a
          -> l:{AVLL a x | leftHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLL v (Node lv ll lr _) r = mkNode lv ll (mkNode v lr r)

{-@ balLR :: x:a
          -> l:{AVLL a x | rightHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r 
  = mkNode lrv (mkNode lv ll lrl) (mkNode v lrr r)

-- Exercise 12.4

{-@ balR0 :: x:a
          -> l: AVLL a x
          -> r: {AVLR a x | rightBig l r && noHeavy r}
          -> AVLN a {realHeight r + 1}
  @-}
balR0 v l (Node rv rl rr _) = mkNode rv (mkNode v l rl) rr

-- Exercise 12.5

{-@ balRR :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && rightHeavy r}
          -> AVLT a r
  @-}
balRR v l (Node rv rl rr _) = mkNode rv (mkNode v l rl) rr

-- Exercise 12.6

{-@ balRL :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && leftHeavy r}
          -> AVLT a r
  @-}
balRL v l (Node rv (Node rlv rll rlr _ ) rr _) 
  = mkNode rlv (mkNode v l rll) (mkNode rv rlr rr)

--

{-@ insert :: a -> s:AVL a -> {t:AVL a | eqOrUp s t} @-}
insert y Leaf = singleton y
insert y t@(Node x _ _ _)
  | y < x     = insL y t
  | y > x     = insR y t
  | otherwise = t

{-@ inline eqOrUp @-}
eqOrUp s t = d == 0 || d == 1
  where
    d      = diff t s

{-@ insL :: x:a
         -> t:{AVL a | x < key t && 0 < realHeight t}
         -> {v: AVL a | eqOrUp t v}
  @-}
insL a (Node v l r _)
  | isLeftBig && leftHeavy l'  = balLL  v l' r
  | isLeftBig && rightHeavy l' = balLR  v l' r
  | isLeftBig                  = balL0  v l' r
  | otherwise                  = mkNode v l' r
  where
    isLeftBig                  = leftBig l' r
    l'                         = insert a l

-- Exercise 12.6

{-@ insR :: x:a
         -> t:{AVL a  | key t < x && 0 < realHeight t }
         -> {v: AVL a | eqOrUp t v}
  @-}
insR a (Node v l r _)
  | isRightBig && leftHeavy r'  = balRL  v l r'
  | isRightBig && rightHeavy r' = balRR  v l r'
  | isRightBig                  = balR0  v l r'
  | otherwise                   = mkNode v l r'
  where
    isRightBig                  = rightBig l r'
    r'                          = insert a r  

--

{-@ bal :: x:a
        -> l:AVLL a x
        -> r:{AVLR a x | isBal l r 2}
        -> {t:AVL a | reBal l r t}
  @-}
bal v l r
  | isLeftBig  && leftHeavy l  = balLL  v l r
  | isLeftBig  && rightHeavy l = balLR  v l r
  | isLeftBig                  = balL0  v l r
  | isRightBig && leftHeavy r  = balRL  v l r
  | isRightBig && rightHeavy r = balRR  v l r
  | isRightBig                 = balR0  v l r
  | otherwise                  = mkNode v l r
  where
    isLeftBig                  = leftBig  l r
    isRightBig                 = rightBig l r

{-@ inline reBal @-}
reBal l r t = bigHt l r t && balHt l r t

{-@ inline balHt @-}
balHt l r t = not (isBal l r 1) || isReal (realHeight t) l r

{-@ inline bigHt @-}
bigHt l r t = lBig && rBig
  where
    lBig    = not (hl >= hr) || (eqOrUp l t)
    rBig    = (hl >= hr)     || (eqOrUp r t)
    hl      = realHeight l
    hr      = realHeight r

{-@ insert' :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insert' a t@(Node v l r _)
  | a < v      = bal v (insert' a l) r
  | a > v      = bal v l (insert' a r)
  | otherwise  = t
insert' a Leaf = singleton a

--

{-@ delete :: a -> s:AVL a -> {t:AVL a | eqOrDn s t} @-}
delete y (Node x l r _)
  | y < x     = bal x (delete y l) r
  | x < y     = bal x l (delete y r)
  | otherwise = merge x l r
delete _ Leaf = Leaf

{-@ inline eqOrDn @-}
eqOrDn s t = eqOrUp t s

{-@ merge :: x:a 
          -> l:AVLL a x 
          -> r:{AVLR a x | isBal l r 1} 
          -> {t:AVL a | bigHt l r t} 
  @-}
merge :: a -> AVL a -> AVL a -> AVL a
merge _ Leaf r = r
merge _ l Leaf = l
merge x l r = bal y l r'
  where
    P y r' = getMin r

-- I'd would want to express:

-- {-@ getMin :: s:{AVL a | realHeight s > 0} -> (x:a, {t:AVLR a | eqOrDn s t}) @-}

{-@ getMin :: s:{AVL a | realHeight s > 0} -> p:{PairET a | eqOrDn s (tree p)} @-}
getMin (Node x Leaf r _) = P x r
getMin (Node x l    r _) = P x' (bal x l' r)
  where
    P x' l' = getMin l

{-@ data PairET a = P {
        elem :: a
      , tree :: AVLR a elem
      }
  @-}
data PairET a = P {
    elem :: a
  , tree :: AVL a
}
