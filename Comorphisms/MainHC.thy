theory MainHC = Main

consts app :: "('a => 'b option) option => 'a option => 'b option"

primrec
  "app None a = None"
  "app (Some f) a = (case a of 
                            None => None
                          | Some x => f x)"

consts  defOp :: "'a option=> bool"
primrec
  "defOp (Some x) = True"
  "defOp None     = False"