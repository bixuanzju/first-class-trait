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
         | And Exp Exp
         | Or Exp Exp


-- Evaluator
evaluate :: Exp -> Env -> Maybe Value
evaluate (B b) _ = Just (BoolV b)
evaluate (If e1 e2 e3) env = do
  (BoolV f) <- evaluate e1 env
  a <- evaluate e2 env
  b <- evaluate e3 env
  return (if f then a else b)
evaluate (And e1 e2) env = do
  (BoolV e1') <- evaluate e1 env
  (BoolV e2') <- evaluate e1 env
  return (BoolV (e1' && e2'))
evaluate (Or e1 e2) env = do
  (BoolV e1') <- evaluate e1 env
  (BoolV e2') <- evaluate e1 env
  return (BoolV (e1' || e2'))




-- Pretty printer
pretty :: Exp -> String
pretty (B b) = show b
pretty (If e1 e2 e3) = "(if " ++ pretty e1 ++ " then " ++ pretty e2 ++ " else " ++ pretty e3 ++ ")"
pretty (And exp1 exp2) = "(" ++ pretty exp1 ++ " && " ++ pretty exp2 ++ ")"
pretty (Or exp1 exp2) = "(" ++ pretty exp1 ++ " || " ++ pretty exp2 ++ ")"
