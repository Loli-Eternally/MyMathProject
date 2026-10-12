/-
Lean 证明小操场（只用 Lean 自带库，无需额外下载）。

怎么玩：
1. 点击下面某个 `by` 后面，把光标移到证明步骤上。
2. 按 Ctrl + Shift + Enter 打开 Lean InfoView，查看当前待证明的目标。
3. 逐行移动光标，观察每一步怎样改变目标。
4. 可以把第一个例子里的 5 改成 6：红线表示证明失败；改回 5 就能通过。

注意：`#eval` 用于计算；`theorem` / `example` 则要求 Lean 检查证明。
下面所有证明都已完成，没有用 `sorry` 跳过验证。
-/

namespace MyMathProject.Demo

-- 一、计算式的证明：两边算出来相同，`rfl` 就能完成。
example : 2 + 3 = 5 := by
  rfl

-- 二、带变量的证明：这句话对每个自然数 n 都成立。
-- 自然数加法的定义规定 n + 0 = n，因此也能用 `rfl`。
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

-- 三、逻辑证明：已知 P 和 Q 同时成立，证明 Q 和 P 也同时成立。
-- `constructor` 把目标拆成两部分；`exact` 提交对应的证明。
theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

-- 四、数学归纳法：证明 0 + n = n。
-- 加法按右侧参数递归定义，因此这里用归纳法展示完整的推理过程。
theorem zero_add_by_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- 起点：0 + 0 = 0。
    rfl
  | succ k ih =>
    -- ih 是归纳假设：0 + k = k。
    -- 按加法定义，目标可写成“等式两边各加一个后继”。
    show Nat.succ (0 + k) = Nat.succ k
    -- 用归纳假设替换 0 + k，目标随即完成。
    rw [ih]

-- 五、使用刚证明的定理，而不用重新写一遍证明。
example : 0 + 100 = 100 := by
  exact zero_add_by_induction 100

-- 把光标放在这些命令所在行，InfoView 会显示它们的结果。
#eval 2 + 3
#check add_zero
#check and_swap
#check zero_add_by_induction

/-
建议尝试（先修改上面已有的证明，观察反馈）：
• 把 2 + 3 = 5 改成 7 + 8 = 15，`rfl` 还能通过吗？
• 在 and_swap 中交换 h.right 与 h.left，看看 Lean 提示的类型不匹配。
• 暂时删掉归纳证明的 `rw [ih]`，查看尚未解决的目标，再补回来。

保存后，在项目根目录运行 `lake build`，可以检查整个项目。
-/

end MyMathProject.Demo
