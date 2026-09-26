# withdraw: take amt out of bal, but only when it is covered.
#
#   bend examples/withdraw/main.bend

import Base

def withdraw.go(ok: Bool, bal: U32, amt: U32) -> U32:
  match ok:
    case True{}:
      (bal - amt : U32)
    case False{}:
      bal

def withdraw(+bal: U32, +amt: U32) -> U32:
  withdraw.go((amt <= bal : U32), bal, amt)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(withdraw(100, 30)))
    IO.print(U32.show(withdraw(30, 100)))
    IO.print(U32.show(withdraw(4294967295, 4294967295)))
