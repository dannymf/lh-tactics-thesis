module Options where 

data Options = Options {
  generate_tactic_encoding :: Bool,
  generate_tactic_dir :: Bool
}

defaultOptions = Options {
  generate_tactic_encoding = False,
  generate_tactic_dir = False
}
