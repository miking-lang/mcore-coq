lang ArithLang 
  syn Expr =
  | TmInt Int
  | TmIncr Expr
  | TmAdd {lhs : Expr, rhs : Expr}

  sem desugar =
  | TmInt v -> TmInt v
  | TmAdd t -> TmAdd {lhs = desugar t.lhs, 
                      rhs = desuagar t.rhs}
  | TmIncr e -> TmAdd {lhs = desugar e,
                       rhs = TmInt 1}

  sem eval = 
  | TmInt x -> x
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)
end