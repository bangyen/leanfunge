/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/-!
# Instructions

## Main definitions

* `Instruction`: The Befunge-93 instruction set.
* `decodeChar`: Decode a playfield character into an instruction.
-/

namespace LeanFunge

/-- A single Befunge instruction. -/
inductive Instruction where
  | push (n : Int)        -- `0`-`9`: push a digit
  | add                   -- `+`: addition
  | sub                   -- `-`: subtraction
  | mul                   -- `*`: multiplication
  | div                   -- `/`: integer division
  | mod                   -- `%`: modulo
  | not                   -- `!`: logical not
  | greater               -- `` ` ``: greater than
  | right                 -- `>`: move right
  | left                  -- `<`: move left
  | up                    -- `^`: move up
  | down                  -- `v`: move down
  | chooseH               -- `_`: horizontal choice
  | chooseV               -- `|`: vertical choice
  | random                -- `?`: random direction
  | stringMode            -- `"`: toggle string mode
  | dup                   -- `:`: duplicate top of stack
  | swap                  -- `\`: swap top two elements
  | drop                  -- `$`: discard top of stack
  | printInt              -- `.`: print integer
  | printChar             -- `,`: print character
  | trampoline            -- `#`: skip the next cell
  | put                   -- `p`: store a value in the playfield
  | get                   -- `g`: fetch a value from the playfield
  | inputInt              -- `&`: read an integer
  | inputChar             -- `~`: read a character
  | halt                  -- `@`: end the program
  | nop                   -- any other character
  deriving DecidableEq, Repr

/-- Decode a playfield character into an instruction. -/
def decodeChar : Char → Instruction
  | '0' => .push 0
  | '1' => .push 1
  | '2' => .push 2
  | '3' => .push 3
  | '4' => .push 4
  | '5' => .push 5
  | '6' => .push 6
  | '7' => .push 7
  | '8' => .push 8
  | '9' => .push 9
  | '+' => .add
  | '-' => .sub
  | '*' => .mul
  | '/' => .div
  | '%' => .mod
  | '!' => .not
  | '`' => .greater
  | '>' => .right
  | '<' => .left
  | '^' => .up
  | 'v' => .down
  | '_' => .chooseH
  | '|' => .chooseV
  | '?' => .random
  | '"' => .stringMode
  | ':' => .dup
  | '\\' => .swap
  | '$' => .drop
  | '.' => .printInt
  | ',' => .printChar
  | '#' => .trampoline
  | 'p' => .put
  | 'g' => .get
  | '&' => .inputInt
  | '~' => .inputChar
  | '@' => .halt
  | _ => .nop

end LeanFunge
