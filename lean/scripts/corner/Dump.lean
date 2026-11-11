import FixedNoiseErgodicity.Scaffold.Format
open FNE.Scaffold
def thinS : Thin → String | .a => "a" | .b => "b" | .c => "c" | .d => "d"
def thickS : Thick → String
  | .corner .a => "Ca" | .corner .b => "Cb" | .corner .c => "Cc" | .corner .d => "Cd"
  | .line _ _ => "L"
def blackS : Black → String | .A => "A" | .B => "B" | .C => "C" | .D => "D" | .E => "E"
#eval (Letter.letters.map fun x =>
  s!"{thinS x.base.thin} {thickS x.base.thick} {blackS x.base.black} {x.b1.toNat} {x.b2.toNat} {x.codeN} {x.codeE} {x.codeS} {x.codeW}") |> String.intercalate "\n" |> IO.println
