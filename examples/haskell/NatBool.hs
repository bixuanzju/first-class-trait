data Type
  = TInt
  | TBool
  deriving (Eq, Show)

data Value = IntV  Int
           | BoolV Bool
           deriving Eq

type TEnv = [(String,Type)]

type Env = [(String, Value)]

-- AST
data Exp = Num Int
         | Add Exp Exp
         | Sub Exp Exp
         | Mult Exp Exp
         | Div Exp Exp
         | B Bool
         | If Exp Exp Exp

-- Evaluator
evaluate :: Exp -> Env -> Maybe Value
evaluate (Num n) _ = Just (IntV n)
evaluate (Add a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av + bv))
evaluate (Sub a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av - bv))
evaluate (Mult a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return ((IntV (av * bv)))
evaluate (Div a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av `div` bv))
evaluate (B b) _ = Just (BoolV b)
evaluate (If e1 e2 e3) env = do
  (BoolV f) <- evaluate e1 env
  a <- evaluate e2 env
  b <- evaluate e3 env
  return (if f then a else b)


-- Type checker
tcheck :: Exp -> TEnv -> Maybe Type
tcheck (Num _) _ = Just TInt
tcheck (Add a b) env =
  case (tcheck a env, tcheck b env) of
    (Just TInt, Just TInt) -> Just TInt
    _ -> Nothing
tcheck (Sub a b) env =
  case (tcheck a env, tcheck b env) of
    (Just TInt, Just TInt) -> Just TInt
    _ -> Nothing
tcheck (Mult a b) env =
  case (tcheck a env, tcheck b env) of
    (Just TInt, Just TInt) -> Just TInt
    _ -> Nothing
tcheck (Div a b) env =
  case (tcheck a env, tcheck b env) of
    (Just TInt, Just TInt) -> Just TInt
    _ -> Nothing
tcheck (B _) _ = Just TBool
tcheck (If e1 e2 e3) env =
  case (tcheck e1 env) of
    Just TBool ->
      case (tcheck e2 env, tcheck e3 env) of
        (Just t1, Just t2)
          | t1 == t2 -> Just t1
        _ -> Nothing
    _ -> Nothing


-- Pretty printer
pretty :: Exp -> String
pretty (Num n) = show n
pretty (Add exp1 exp2) = "(" ++ pretty exp1 ++ " + " ++ pretty exp2 ++ ")"
pretty (Sub exp1 exp2) = "(" ++ pretty exp1 ++ " - " ++ pretty exp2 ++ ")"
pretty (Mult exp1 exp2) = "(" ++ pretty exp1 ++ " * " ++ pretty exp2 ++ ")"
pretty (Div exp1 exp2) = "(" ++ pretty exp1 ++ " / " ++ pretty exp2 ++ ")"
pretty (B b) = show b
pretty (If e1 e2 e3) = "(if " ++ pretty e1 ++ " then " ++ pretty e2 ++ " else " ++ pretty e3 ++ ")"
