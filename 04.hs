import Data.List (intercalate, union)

data Term = Variable String | Not Term | Implies Term Term
  deriving Eq

instance Show Term where
  show (Variable c) = c
  show (Not t@(Implies _ _)) = "¬(" ++ show t ++ ")"
  show (Not t) = "¬" ++ show t
  show (Implies t@(Implies _ _) u) = "(" ++ show t ++ ") → " ++ show u
  show (Implies t u) = show t ++ " → " ++ show u

type Antecedents = [Term]
type Consequent = Term

data Proof = Proof Antecedents Consequent

instance Show Proof where
  show (Proof a c) = intercalate ", " (map show a) ++ " ⊢ " ++ show c

(-->) :: Term -> Term -> Term
a --> b = a `Implies` b

assume :: Term -> Proof
assume t = Proof [t] t

ax1 :: Term -> Term -> Proof
ax1 a b = Proof [] (a --> (b --> a))

ax2 :: Term -> Term -> Term -> Proof
ax2 a b c = Proof [] ((a --> (b --> c)) --> ((a --> b) --> (a --> c)))

ax3 :: Term -> Term -> Proof
ax3 a b = Proof [] ((Not a --> Not b) --> (b --> a))

mp :: Proof -> Proof -> Proof
mp (Proof a1 c1) (Proof a2 (c1a `Implies` c1b))
  | c1 == c1a = Proof (a1 `union` a2) c1b
  | otherwise = error "Modus ponens: Premise does not match antecedent."
mp _ _ = error "Modus ponens: Second argument is not an implication proof."

-- Not p |- p -> q
proof :: Term -> Term -> Proof
proof p q = mp (mp np a1) a3 where
  np = assume (Not p)
  a1 = ax1 (Not p) (Not q)
  a3 = ax3 q p

main :: IO ()
main = print $ proof a b where
  a = Variable "a"
  b = Variable "b"
