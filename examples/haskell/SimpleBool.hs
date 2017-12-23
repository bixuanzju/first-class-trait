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
data Exp = B Bool
         | If Exp Exp Exp


-- Evaluator
evaluate :: Exp -> Env -> Maybe Value
evaluate (B b) _ = Just (BoolV b)
evaluate (If e1 e2 e3) env = do
  (BoolV f) <- evaluate e1 env
  a <- evaluate e2 env
  b <- evaluate e3 env
  return (if f then a else b)


-- Pretty printer
pretty :: Exp -> String
pretty (B b) = show b
pretty (If e1 e2 e3) = "(if " ++ pretty e1 ++ " then " ++ pretty e2 ++ " else " ++ pretty e3 ++ ")"
