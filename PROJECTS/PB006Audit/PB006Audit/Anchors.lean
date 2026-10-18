import PB006Audit.Basic

namespace PB006Audit

theorem empty_decide : weightedBell [] = 1 := by decide
theorem singleton_decide : weightedBell [2] = 2 := by decide

theorem a112_decide : weightedBell [1, 1, 2] = 7 := by decide
theorem a22_decide : weightedBell [2, 2] = 7 := by decide
theorem a222_decide : weightedBell [2, 2, 2] = 31 := by decide
theorem a24_decide : weightedBell [2, 4] = 9 := by decide
theorem a33_decide : weightedBell [3, 3] = 8 := by decide

theorem a112_native : weightedBell [1, 1, 2] = 7 := by native_decide
theorem a22_native : weightedBell [2, 2] = 7 := by native_decide
theorem a222_native : weightedBell [2, 2, 2] = 31 := by native_decide
theorem a24_native : weightedBell [2, 4] = 9 := by native_decide
theorem a33_native : weightedBell [3, 3] = 8 := by native_decide

end PB006Audit
