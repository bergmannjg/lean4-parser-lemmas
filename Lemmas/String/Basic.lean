module

import Init.Meta

import all Init.Data.String.Basic

public section

namespace Parser.String.Slice

@[simp] theorem castSliceStartInclusive (s1 s2 : String.Slice) (h1 : s1.str = s2.str)
  (h2 : s1.startInclusive.offset = s2.startInclusive.offset)
    : s1.startInclusive.cast h1 = s2.startInclusive := by
  exact (String.Pos.ext h2)

@[simp] theorem castSliceEndExclusive (s1 s2 : String.Slice) (h1 : s1.str = s2.str)
  (h2 : s1.endExclusive.offset = s2.endExclusive.offset)
    : s1.endExclusive.cast h1 = s2.endExclusive := by
  exact (String.Pos.ext h2)
