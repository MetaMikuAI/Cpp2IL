# ARM64 HFA / 栈接收者恢复审计（2026-09-24）

## 范围与结论

- 修复：平坦、同质 1–4 个 float/double 字段的 ARM64 HFA 调用边界；在调用点重新绑定可证明的标量栈接收者地址。没有游戏类型特调。
- 检查 24 个文件中的 24 个方法的诊断增量；其中 8 个方法进一步核对 objdump 汇编。未使用 IDA。
- 23 个样本的诊断增量主要可归因于旧输出丢失的数据流被恢复；1 个混合风险单列。不是“23 个方法已完全正确”，也不是全量无回退保证。
- 选样：高 Note 增幅文件候选 + 固定种子 20260924 打乱其余候选；从能配对的方法中选增量最大者，共 21 个 Note 样本；另加 3 个 IL/Unknown 增量样本。存在选择偏差，不能把 23/24 外推为总体正确率。
- 全量逐文件归一化诊断消息（仅消除 SSA 编号）做 Counter 差集：新增 2581 条，其中静态字段基址 1173、静态字段 1074、其他内存读取 331、其他诊断 3。前两类合计 2247/2581=87.1%。这只是结构分类，不是逐条语义证明；也不等于 Note 净增 2348。

## 已知风险（本次保留）

1. `FenceEditPlanningState.OnReceivePinchInOutEventData` 的结构体参数字段赋值出现在构造调用之后。原输出也错误，但新输出不能视为单纯无害的诊断增加；应继续检查构造恢复与合成聚合值的指令顺序。
2. 静态/嵌套结构体字段、条件地址、结构体数组元素仍可能变成 NoteDecompilerIssue、零值或非法类型转换。
3. 此次只覆盖可证明的平坦 HFA；复杂嵌套布局、部分间接/接口调用、SIMD 分量和构造/聚合恢复的交互仍有覆盖缺口。
4. 行数 2139352→2192057；不是可以直接编译运行的完整还原。不要根据空 if 减少或 perfect 增加推断语义已正确。

## 样本记录

| # | 文件 / 方法 | ΔNote | ΔIL | 增量来源与保留风险 |
|---|---|---:|---:|---|
| 1 | `Assembly-CSharp/Sekai/LiveTransitioner.cs` / `LiveTransitioner / public void PlayWhiteOut(Action onFinish, bool showsLoading = false, float timeout = 0f, float delay = 1f, float duration = 1f)` | +6 | +6 | 旧 Set((Color)0) 和 Play 参数错位；新增项为静态颜色 RGBA 读取。 |
| 2 | `Assembly-CSharp/Sekai.Ik/LookAtCore.cs` / `LookAtCore / private unsafe void LookUpdateImpl(in Vector3 targetPosition)` | +28 | -4 | 新增 28 条均为 Vector3 静态基址/分量读取；旧 TransformVector/Quaternion 调用大量使用零占位。复杂数学与接收者问题仍未解决。 |
| 3 | `Assembly-CSharp/Sekai/ScenarioPlayer.cs` / `ScenarioPlayer / private unsafe void LoadLayoutEffect(ScenarioCueData cueData)` | +7 | +7 | 旧 ColorFader.Set((Color)0)；新增项来自 BLACK/WHITE 颜色及 Vector3 静态分量。 |
| 4 | `Assembly-CSharp/Sekai/ColorUtility.cs` / `ColorUtility / public static Color GetChangedValueTextColor(int current, int changed, Color defaultColor)` | +8 | +9 | 旧返回 (Color)current/typeof(ColorUtility)；现恢复 defaultColor 与正负颜色选择，静态分量仍未解析。 |
| 5 | `Assembly-CSharp/Sekai.MusicScoreMaker.Ingame.Views/SelectedObjectEditUIView.cs` / `SelectedObjectEditUIView / private bool CheckPositionFitsInScreen()` | +4 | -1 | 旧 InverseTransformPoint((Vector3)0)；现暴露数组元素 x/z 读取，汇编证实 0x20/24/28、0x38/3c/40 分量。 |
| 6 | `Assembly-CSharp/Sekai.UI.Dialog/SelectEventRelatedMusicDialog.cs` / `SelectEventRelatedMusicDialog / private IEnumerator ForBackKey()` | +4 | +0 | 旧 normalizedPosition=(Vector2)0；现暴露 Vector2.oneVector 静态分量，两次写入对应两组诊断。 |
| 7 | `Assembly-CSharp/Sekai.Core.Rendering/RenderUtility.cs` / `RenderUtility / public unsafe static (Color, Vector4) GetFlareLightFactor(RenderLightingParameter parameter, Camera camera)` | +1 | -1 | 旧归一化分支为空，位置依赖 default(object)；现恢复运算并暴露零向量分支的静态基址。元组输出仍有问题。 |
| 8 | `Assembly-CSharp/Sekai/UIPartsBondsHonorSettingCharacter.cs` / `UIPartsBondsHonorSettingCharacter / public void SetSlot(HonorSlot slotType)` | +11 | +2 | 旧 localScale/anchoredPosition 为零占位；新增项全部为 Vector3 静态基址/分量。其余缩放数学未作完整正确性证明。 |
| 9 | `Assembly-CSharp/Sekai.UI/CardUnitInfo.cs` / `CardUnitInfo / LogoSetting / public void Setup(UnitType unitType, CardViewDataBase.CardUnitType cardUnitType)` | +3 | +7 | 旧三个空分支、localScale/anchoredPosition 零占位；现暴露条件选择字段偏移的间接读取。 |
| 10 | `Assembly-CSharp/Sekai.CustomProfile/DynamicContentView.cs` / `DynamicContentView / public void SetViewInfo(Texture texture, Rect uvRect, float viewportSize)` | +2 | -1 | 旧 uvRect、sizeDelta 零占位及空尺寸判断；现保留 Rect 分量/viewportSize，暴露 Vector2.one 静态读取。 |
| 11 | `Assembly-CSharp/Sekai/CharacterRankExpRewardDialog.cs` / `CharacterRankExpRewardDialog / protected override void OpenAnimation()` | +2 | +1 | 旧 Color 被错当成 duration 参数；现 Color 分量与两个 float 参数分离，新增静态 b/a 分量诊断。 |
| 12 | `Assembly-CSharp/Sekai/TreeTalkBalloonController.cs` / `TreeTalkBalloonController / public TreeTalkBalloon Show(Transform target, Vector2 offset, string text)` | +3 | +2 | 旧 offset/Camera/string 参数错位且 localScale 零占位；汇编证实独立浮点参数与 Vector3.one 静态读取。 |
| 13 | `Assembly-CSharp/Sekai.MusicScoreMaker.Outgame/MusicScoreListCellHighlightContents.cs` / `MusicScoreListCellHighlightContents / private void UpdatePosition(bool hasMarker)` | +6 | +14 | 旧条件分支为空且三处坐标置零；汇编证实 CSEL 选择偏移后 LDR s0/s1，新诊断是尚未恢复的动态字段偏移。 |
| 14 | `Assembly-CSharp/Sekai.Mysekai/UIPartsFixtureThumbnail.cs` / `UIPartsFixtureThumbnail / public void UpdateQuantity(int newQuantity)` | +5 | +12 | 旧四个空分支及 SetQuantityWithColor(...,(Color)0)；现暴露条件颜色的静态基址和四分量读取。 |
| 15 | `Assembly-CSharp/Sekai.Mysekai/SiteMapIcon.cs` / `SiteMapIcon / public override void Setup(Action<MysekaiSiteType> onMoveSiteMap)` | +3 | +1 | 旧位置默认值、DOScale 的 Vector3/duration 错位；现恢复位置分量和 0.3f duration，新增静态 oneVector 读取。 |
| 16 | `Assembly-CSharp/Sekai.Mysekai/FenceEditPlanningState.cs` / `FenceEditPlanningState / public unsafe void OnReceivePinchInOutEventData(GestureEventData data)` | +1 | +1 | 混合风险：新增 Note 来自旧隐藏的 Vector3.zero 读取；但输出将 position 字段赋值放到构造调用之后。汇编 0x56cb5b4..5cc 先准备 s0..s2 再调用，与当前 C# 顺序不符。未修复，不归为纯暴露。 |
| 17 | `Assembly-CSharp/Sekai.SuperVirtualLive/RoomLinkStamp.cs` / `RoomLinkStamp / protected override void OnReceiveFromOtherRoom(ref MessagePacketData receiveData)` | +2 | +2 | 旧 ActionParam 的 vectorParam 为零占位；汇编确认从 this+0x50/54/58 读取嵌入向量，新增 y/z 诊断不是凭空引入的读取。 |
| 18 | `Assembly-CSharp/Sekai.Mysekai/FieldCameraStateBase.cs` / `FieldCameraStateBase / protected unsafe void UpdateCameraCollision(float modelMinDistance)` | +1 | -6 | 旧 Quaternion/Vector3/Raycast 参数错位和空归一化分支；现恢复多个分量/参数，新增 Note 为归一化失败分支的静态零向量。 |
| 19 | `Assembly-CSharp/Sekai.Core/SekaiCharacterRimLight.cs` / `SekaiCharacterRimLight / private void OnDrawGizmos()` | +3 | -8 | 旧 DrawCube/DrawRay 坐标为零占位；新增三条均为 Vector3.one 静态基址/y/z 读取。 |
| 20 | `Assembly-CSharp/Sekai/ScreenLayerEventStorySelect.cs` / `ScreenLayerEventStorySelect / protected override void CreateStoryList()` | +2 | +2 | 旧 SetContentPosition((Vector2)1)；现恢复 pos 与 snapSkip:true，暴露 Vector2.up 静态分量。 |
| 21 | `Assembly-CSharp/Sekai.MusicScoreMaker.Ingame.Views/LongNoteLinePreview.cs` / `LongNoteLinePreview / private void PopulateStraightMesh(VertexHelper vh)` | +4 | +4 | 旧 AddVert 将 Color32 当 Vector3、UV 为默认；汇编确认嵌入向量的 y 分量 0x120/128/130/138，新增四条对应这些读取。颜色转换方法仍未找到。 |
| 22 | `Assembly-CSharp/Sekai.Avatar/AvatarBase.cs` / `AvatarBase / protected unsafe void SetRightPenlightColor(PenlightColorData colorData)` | +0 | +19 | 旧空颜色选择分支和 SetColor(...,(Color)0)；现暴露两种模型各四个字段地址，新增 Unknown/Expected 来自未消解的地址运算。 |
| 23 | `Assembly-CSharp/Sekai/TweenColor.cs` / `TweenColor / public unsafe override void PlayCore(PlayDirection playDirection)` | +0 | +14 | 旧终值为 (Color)0、duration 被颜色分量替代；现暴露四分量字段地址，接口 Color setter 仍未恢复。 |
| 24 | `Assembly-CSharp/Sekai.Mysekai.ContentList/ContentListSelectorCell.cs` / `ContentListSelectorCell / protected override Color GetTextColor(bool isSelected)` | +0 | +20 | 旧空 if 加 return (Color)this；汇编确认按条件取 this+0x90..9c 或 0xa0..ac 并通过 s0..s3 返回。新诊断来自未消解的字段地址。 |

## 验证与全量统计

- Analysis：872/872；ISIL：173/173；git diff --check 通过。端到端由源码重新构建、导出完整 Assembly-CSharp，11231 文件，失败程序集 0，已清理中间 DLL。
- 目标 LiveCategoryVoicePageView.UpdateCellsAsync：空 if 2→0，保留旧纵坐标，横坐标由 index 奇偶决定；20005 个含 Int32 边界的整数样本验证底层表达式等价于 C# index%2。
- perfect 5301→5428；IL 95995→93964；Note 32928→35276；Unmanaged loads 19991→22379；Method not found 10470→10434；Unknown 17626→17563；Expected 78089→76270；nint 32224→35173；空 if 1021→576。
- 转义标记两种各 120271→120256；Stack unsettled 3、Func<object> 113、IEnumerable<object> 46 不变。
- 工作区证据（不纳入源码仓库）：`logs/position-samples.json`、`logs/position-samples.diff`、`logs/position-native-audit/`（8 个方法汇编）、`logs/position-diagnostic-categories.json`、`logs/position-audit.md`、`logs/position-regressions.md`。
