import IrForge
/-- Prints the compiled `vk 1`; the kernel proved `vk 1 = false` (`vk_one`). -/
def main (args : List String) : IO Unit :=
  IO.println s!"compiled vk {args.length + 1} = {vk (args.length + 1)}"
