-- Inspired by:
-- "Interpreting types as abstract values",
-- Oleg Kiselyov (FNMOC) and Chung-chieh Shan (Rutgers University),
-- http://okmij.org/ftp/Computation/FLOLAC/

import Control.Applicative ((<|>))
import Control.Monad.Error (ErrorT, runErrorT, throwError)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (StateT, get, put, runStateT)
import Data.Attoparsec.ByteString.Char8
import Data.ByteString.Char8 (pack)
import Data.Char (chr, ord)

type TVarId = Int

data Type = TVar TVarId | Type :> Type
  deriving Eq
infixr 9 :>

instance Show Type where
  show (TVar v) = [chr $ v + ord 'A']
  show ((s :> t) :> u) = "(" ++ show s ++ " -> " ++ show t ++ ")" ++ " -> " ++ show u
  show (s :> t) = "" ++ show s ++ " -> " ++ show t

type Substitution = (TVarId, Type)

-- | Substitute recursively in a type.
substTree :: [Substitution] -> Type -> Type
substTree ss (t1 :> t2) = substTree ss t1 :> substTree ss t2
substTree ss t = substRoot ss t

-- | Substitute only the root of a type.
substRoot :: [Substitution] -> Type -> Type
substRoot ss (TVar v) | Just t <- lookup v ss = substRoot ss t
substRoot _ t = t

-- | Obtain the type variables of a type modulo substitution.
vars :: Type -> [Substitution] -> [TVarId]
vars (s :> t) ss = vars s ss ++ vars t ss
vars (TVar v) ss
  | Just t <- lookup v ss = vars t ss
  | otherwise = [v]


-- -----------------------------------------------------------------------------
-- Type unification

data UnifyError = OccursCheck TVarId
type UnifyResult = Either UnifyError [Substitution]

instance Show UnifyError where
  show (OccursCheck _) = "Occurs check"

unifySubst :: Type -> Type -> [Substitution] -> UnifyResult
unifySubst s t ss = unify (substRoot ss s) (substRoot ss t) ss

unify :: Type -> Type -> [Substitution] -> UnifyResult
unify (s1 :> s2) (t1 :> t2) ss = unifySubst s1 t1 ss >>= unifySubst s2 t2
unify (TVar v) t ss = unifyVar v t ss
unify t (TVar v) ss = unifyVar v t ss

unifyVar :: TVarId -> Type -> [Substitution] -> UnifyResult
unifyVar v t@(TVar v') ss
  | v  ==  v' = return ss
  | otherwise = return $ (v, t) : ss
unifyVar v t ss
  | v `elem` vars t ss = Left $ OccursCheck v
  | otherwise = return $ (v, t) : ss


-- -----------------------------------------------------------------------------
-- Type inference

type VarId = String
data Term = V VarId | L VarId Term | A Term Term
  deriving Show

type Typing = (VarId, Type)

type TypeState = (TVarId, [Substitution])

type TypeT e m = StateT TypeState (ErrorT e m)
type TypeM = TypeT String Identity

runTypeT :: TypeT e m a -> TypeState -> m (Either e (a, TypeState))
runTypeT m = runErrorT . runStateT m

runTypeM :: TypeM a -> TypeState -> Either String (a, TypeState)
runTypeM m = runIdentity . runTypeT m

-- | Return a fresh type variable.
freshType :: TypeM Type
freshType = do
  (v, ss) <- get
  put (succ v, ss)
  return $ TVar v

guardUnify :: Type -> Type -> TypeM ()
guardUnify s t = do
  (v, ss) <- get
  either (throwError . show) (\ ss' -> put (v, ss')) $ unifySubst s t ss
  

inferType :: Term -> [Typing] -> TypeM Type
inferType (V v) ty
  | Just t <- lookup v ty = return t
  | otherwise = throwError $ "Unbound variable: " ++ v
inferType (L v t) ty = do
  tv <- freshType
  tt <- inferType t ((v, tv):ty)
  return (tv :> tt)
inferType (A s t) ty = do
  ts <- inferType s ty
  tt <- inferType t ty
  tu <- freshType
  guardUnify ts (tt :> tu)
  return tu


runInferType :: Term -> Either String Type
runInferType term = do
  (t, (_, ss)) <- runTypeM (inferType term []) (0, [])
  return $ substTree ss t


-- -----------------------------------------------------------------------------
-- Parser

termParser :: Parser Term
termParser = app <|> det where
  det = skipSpace >> var <|> lam <|> bra
  var = vid >>= return . V
  lam = char '\\' >> skipSpace >> vid >>= \ v -> skipSpace >> char '.' >>
        termParser >>= \ t -> return $ L v t
  app = det >>= \ t1 -> skipSpace >> termParser >>= return . A t1
  bra = char '(' >> termParser >>= \ t -> char ')' >> return t

  vid = many1 (satisfy $ inClass ['a' .. 'z'])


-- -----------------------------------------------------------------------------
-- Main

intro :: [String]
intro =
  [ "Welcome to λ 1.0."
  , "Type a λ-term. Example: \\x. \\y. x"
  ]

main :: IO ()
main = mapM_ putStrLn intro >> interact (unlines . map verify . lines) where
  verify t = either id result $ parseTerm t >>= runInferType
  result t = "⊢ " ++ show t
  parseTerm = parseOnly termParser . pack
