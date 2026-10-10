import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Drop v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesDropAsciidropV22Server

/-- Buy Sell: one byte code -/
def BuySell.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive BuySell where
  | bought -- Bought
  | sold -- Sold
  | soldShort -- Sold Short
  | soldShortExempt -- Sold Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySell.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySell

def toByte : BuySell → UInt8
  | .bought => 0x42
  | .sold => 0x53
  | .soldShort => 0x54
  | .soldShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySell :=
  if byte = 0x42 then .bought
  else if byte = 0x53 then .sold
  else if byte = 0x54 then .soldShort
  else .soldShortExempt

def ofByte (byte : UInt8) : BuySell :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySell) : ofByte value.toByte = value := by
  cases value with
  | bought => decide
  | sold => decide
  | soldShort => decide
  | soldShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySell) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySell × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySell) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySell

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x41, 0x50, 0x52]

inductive Capacity where
  | agency -- Agency
  | principal -- Principal
  | riskless -- Riskless
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .riskless => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .riskless

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | riskless => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Liquidity Code: one byte code -/
def LiquidityCode.codes : List UInt8 :=
  [0x41, 0x52, 0x58, 0x44, 0x46, 0x47, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x4A, 0x59, 0x53, 0x55, 0x42, 0x45, 0x50, 0x54, 0x5A, 0x57, 0x6D, 0x6B, 0x30, 0x37, 0x38, 0x64, 0x65, 0x66, 0x6A, 0x72, 0x74, 0x34, 0x35, 0x36, 0x67, 0x61, 0x78, 0x79, 0x62, 0x63, 0x68, 0x4E]

inductive LiquidityCode where
  | added -- Added
  | removed -- Removed
  | routed -- Routed
  | dot -- Dot
  | openingTradeOnNyse -- Opening Trade On Nyse
  | onCloseOrderOnNyse -- On Close Order On Nyse
  | openingCross -- Opening Cross
  | openingCrossImbalanceonly -- Opening Cross Imbalanceonly
  | closingCross -- Closing Cross
  | closingCrossImbalanceonly -- Closing Cross Imbalanceonly
  | haltIpoCross -- Halt Ipo Cross
  | haltCross -- Halt Cross
  | nondisplayedAddingLiquidity -- Nondisplayed Adding Liquidity
  | reRoutedByNyse -- Re Routed By Nyse
  | oddLotExecutionOnNyse -- Odd Lot Execution On Nyse
  | addedLiquidityOnNyse -- Added Liquidity On Nyse
  | routedToBx -- Routed To Bx
  | nyseOther -- Nyse Other
  | routedToPsx -- Routed To Psx
  | openingTradeOnArca -- Opening Trade On Arca
  | onCloseOrderOnArca -- On Close Order On Arca
  | addedPostonlyNotCurrentlyAvailable -- Added Postonly Not Currently Available
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | supplementalOrderExecution -- Supplemental Order Execution
  | displayedLiquidityaddingOrderImprovesTheNbbo -- Displayed Liquidityadding Order Improves The Nbbo
  | displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo -- Displayed Liquidityadding Order Sets The Qbbo While Joining The Nbbo
  | retailDesignatedExecutionThatRemovedLiquidityNotCurrentlyAvailable -- Retail Designated Execution That Removed Liquidity Not Currently Available
  | retailDesignatedExecutionThatAddedDisplayedLiquidity -- Retail Designated Execution That Added Displayed Liquidity
  | retailDesignatedExecutionThatAddedNondisplayedLiquidityNotCurrentlyAvailable -- Retail Designated Execution That Added Nondisplayed Liquidity Not Currently Available
  | rpiOrderThatProvidesLiquidity -- Rpi Order That Provides Liquidity
  | retailOrderThatRemovesRpiLiquidity -- Retail Order That Removes Rpi Liquidity
  | retailOrderThatRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity -- Retail Order That Removes Price Improving Nondisplayed Liquidity Other Than Rpi Liquidity
  | addedDisplayedLiquidityInAGroupASymbol -- Added Displayed Liquidity In A Group A Symbol
  | addedNondisplayedLiquidityInAGroupASymbol -- Added Nondisplayed Liquidity In A Group A Symbol
  | liquidityRemovingOrderInAGroupASymbol -- Liquidity Removing Order In A Group A Symbol
  | addedNondisplayedMidpointLiquidityInAGroupASymbol -- Added Nondisplayed Midpoint Liquidity In A Group A Symbol
  | addedDisplayedLiquidityInAScipSymbol -- Added Displayed Liquidity In A Scip Symbol
  | displayedLiquidityaddingOrderImprovesTheNbboInAScipSymbol -- Displayed Liquidityadding Order Improves The Nbbo In A Scip Symbol
  | displayedLiquidityaddingOrderSetTheQbboWhileJoiningTheNbboInAScipSymbol -- Displayed Liquidityadding Order Set The Qbbo While Joining The Nbbo In A Scip Symbol
  | displayedLiquidityaddingOrderImprovesTheNbboInPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe -- Displayed Liquidityadding Order Improves The Nbbo In Pilot Symbol During Specified Luld Pricing Pilot Timeframe
  | addedDisplayedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe -- Added Displayed Liquidity In A Pilot Symbol During Specified Luld Pricing Pilot Timeframe
  | removedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe -- Removed Liquidity In A Pilot Symbol During Specified Luld Pricing Pilot Timeframe
  | haltCrossOrdersEnteredInPilotSymbolsDuringTheLuldTradingPause -- Halt Cross Orders Entered In Pilot Symbols During The Luld Trading Pause
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityCode

def toByte : LiquidityCode → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .routed => 0x58
  | .dot => 0x44
  | .openingTradeOnNyse => 0x46
  | .onCloseOrderOnNyse => 0x47
  | .openingCross => 0x4F
  | .openingCrossImbalanceonly => 0x4D
  | .closingCross => 0x43
  | .closingCrossImbalanceonly => 0x4C
  | .haltIpoCross => 0x48
  | .haltCross => 0x4B
  | .nondisplayedAddingLiquidity => 0x4A
  | .reRoutedByNyse => 0x59
  | .oddLotExecutionOnNyse => 0x53
  | .addedLiquidityOnNyse => 0x55
  | .routedToBx => 0x42
  | .nyseOther => 0x45
  | .routedToPsx => 0x50
  | .openingTradeOnArca => 0x54
  | .onCloseOrderOnArca => 0x5A
  | .addedPostonlyNotCurrentlyAvailable => 0x57
  | .removedLiquidityAtAMidpoint => 0x6D
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .supplementalOrderExecution => 0x30
  | .displayedLiquidityaddingOrderImprovesTheNbbo => 0x37
  | .displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo => 0x38
  | .retailDesignatedExecutionThatRemovedLiquidityNotCurrentlyAvailable => 0x64
  | .retailDesignatedExecutionThatAddedDisplayedLiquidity => 0x65
  | .retailDesignatedExecutionThatAddedNondisplayedLiquidityNotCurrentlyAvailable => 0x66
  | .rpiOrderThatProvidesLiquidity => 0x6A
  | .retailOrderThatRemovesRpiLiquidity => 0x72
  | .retailOrderThatRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => 0x74
  | .addedDisplayedLiquidityInAGroupASymbol => 0x34
  | .addedNondisplayedLiquidityInAGroupASymbol => 0x35
  | .liquidityRemovingOrderInAGroupASymbol => 0x36
  | .addedNondisplayedMidpointLiquidityInAGroupASymbol => 0x67
  | .addedDisplayedLiquidityInAScipSymbol => 0x61
  | .displayedLiquidityaddingOrderImprovesTheNbboInAScipSymbol => 0x78
  | .displayedLiquidityaddingOrderSetTheQbboWhileJoiningTheNbboInAScipSymbol => 0x79
  | .displayedLiquidityaddingOrderImprovesTheNbboInPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => 0x62
  | .addedDisplayedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => 0x63
  | .removedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => 0x68
  | .haltCrossOrdersEnteredInPilotSymbolsDuringTheLuldTradingPause => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityCode :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dot
  else if byte = 0x46 then .openingTradeOnNyse
  else if byte = 0x47 then .onCloseOrderOnNyse
  else if byte = 0x4F then .openingCross
  else if byte = 0x4D then .openingCrossImbalanceonly
  else if byte = 0x43 then .closingCross
  else if byte = 0x4C then .closingCrossImbalanceonly
  else if byte = 0x48 then .haltIpoCross
  else if byte = 0x4B then .haltCross
  else if byte = 0x4A then .nondisplayedAddingLiquidity
  else if byte = 0x59 then .reRoutedByNyse
  else if byte = 0x53 then .oddLotExecutionOnNyse
  else if byte = 0x55 then .addedLiquidityOnNyse
  else if byte = 0x42 then .routedToBx
  else if byte = 0x45 then .nyseOther
  else if byte = 0x50 then .routedToPsx
  else if byte = 0x54 then .openingTradeOnArca
  else if byte = 0x5A then .onCloseOrderOnArca
  else if byte = 0x57 then .addedPostonlyNotCurrentlyAvailable
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else if byte = 0x6B then .addedLiquidityViaAMidpointOrder
  else if byte = 0x30 then .supplementalOrderExecution
  else if byte = 0x37 then .displayedLiquidityaddingOrderImprovesTheNbbo
  else if byte = 0x38 then .displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo
  else if byte = 0x64 then .retailDesignatedExecutionThatRemovedLiquidityNotCurrentlyAvailable
  else if byte = 0x65 then .retailDesignatedExecutionThatAddedDisplayedLiquidity
  else if byte = 0x66 then .retailDesignatedExecutionThatAddedNondisplayedLiquidityNotCurrentlyAvailable
  else if byte = 0x6A then .rpiOrderThatProvidesLiquidity
  else if byte = 0x72 then .retailOrderThatRemovesRpiLiquidity
  else if byte = 0x74 then .retailOrderThatRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity
  else if byte = 0x34 then .addedDisplayedLiquidityInAGroupASymbol
  else if byte = 0x35 then .addedNondisplayedLiquidityInAGroupASymbol
  else if byte = 0x36 then .liquidityRemovingOrderInAGroupASymbol
  else if byte = 0x67 then .addedNondisplayedMidpointLiquidityInAGroupASymbol
  else if byte = 0x61 then .addedDisplayedLiquidityInAScipSymbol
  else if byte = 0x78 then .displayedLiquidityaddingOrderImprovesTheNbboInAScipSymbol
  else if byte = 0x79 then .displayedLiquidityaddingOrderSetTheQbboWhileJoiningTheNbboInAScipSymbol
  else if byte = 0x62 then .displayedLiquidityaddingOrderImprovesTheNbboInPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe
  else if byte = 0x63 then .addedDisplayedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe
  else if byte = 0x68 then .removedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe
  else .haltCrossOrdersEnteredInPilotSymbolsDuringTheLuldTradingPause

def ofByte (byte : UInt8) : LiquidityCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityCode) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | routed => decide
  | dot => decide
  | openingTradeOnNyse => decide
  | onCloseOrderOnNyse => decide
  | openingCross => decide
  | openingCrossImbalanceonly => decide
  | closingCross => decide
  | closingCrossImbalanceonly => decide
  | haltIpoCross => decide
  | haltCross => decide
  | nondisplayedAddingLiquidity => decide
  | reRoutedByNyse => decide
  | oddLotExecutionOnNyse => decide
  | addedLiquidityOnNyse => decide
  | routedToBx => decide
  | nyseOther => decide
  | routedToPsx => decide
  | openingTradeOnArca => decide
  | onCloseOrderOnArca => decide
  | addedPostonlyNotCurrentlyAvailable => decide
  | removedLiquidityAtAMidpoint => decide
  | addedLiquidityViaAMidpointOrder => decide
  | supplementalOrderExecution => decide
  | displayedLiquidityaddingOrderImprovesTheNbbo => decide
  | displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo => decide
  | retailDesignatedExecutionThatRemovedLiquidityNotCurrentlyAvailable => decide
  | retailDesignatedExecutionThatAddedDisplayedLiquidity => decide
  | retailDesignatedExecutionThatAddedNondisplayedLiquidityNotCurrentlyAvailable => decide
  | rpiOrderThatProvidesLiquidity => decide
  | retailOrderThatRemovesRpiLiquidity => decide
  | retailOrderThatRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => decide
  | addedDisplayedLiquidityInAGroupASymbol => decide
  | addedNondisplayedLiquidityInAGroupASymbol => decide
  | liquidityRemovingOrderInAGroupASymbol => decide
  | addedNondisplayedMidpointLiquidityInAGroupASymbol => decide
  | addedDisplayedLiquidityInAScipSymbol => decide
  | displayedLiquidityaddingOrderImprovesTheNbboInAScipSymbol => decide
  | displayedLiquidityaddingOrderSetTheQbboWhileJoiningTheNbboInAScipSymbol => decide
  | displayedLiquidityaddingOrderImprovesTheNbboInPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => decide
  | addedDisplayedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => decide
  | removedLiquidityInAPilotSymbolDuringSpecifiedLuldPricingPilotTimeframe => decide
  | haltCrossOrdersEnteredInPilotSymbolsDuringTheLuldTradingPause => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityCode

/-- Clearing Code: one byte code -/
def ClearingCode.codes : List UInt8 :=
  [0x51]

inductive ClearingCode where
  | qsr -- Qsr
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingCode

def toByte : ClearingCode → UInt8
  | .qsr => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ClearingCode :=
  .qsr

def ofByte (byte : UInt8) : ClearingCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingCode) : ofByte value.toByte = value := by
  cases value with
  | qsr => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearingCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearingCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearingCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClearingCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearingCode

/-- Reference Price Type: one byte code -/
def ReferencePriceType.codes : List UInt8 :=
  [0x20, 0x49]

inductive ReferencePriceType where
  | notApplicable -- Not Applicable
  | intradayIndicativeValue -- Intraday Indicative Value
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceType

def toByte : ReferencePriceType → UInt8
  | .notApplicable => 0x20
  | .intradayIndicativeValue => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferencePriceType :=
  if byte = 0x20 then .notApplicable
  else .intradayIndicativeValue

def ofByte (byte : UInt8) : ReferencePriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceType) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | intradayIndicativeValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceType

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x5A, 0x43, 0x48, 0x58]

inductive CancelReason where
  | userCancel -- User Cancel
  | iocCancel -- Ioc Cancel
  | timeout -- Timeout
  | supervisoryCancel -- Supervisory Cancel
  | regulatoryCancel -- Regulatory Cancel
  | selfMatchPrevention -- Self Match Prevention
  | systemCancel -- System Cancel
  | crossCancel -- Cross Cancel
  | halted -- Halted
  | openProtection -- Open Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .userCancel => 0x55
  | .iocCancel => 0x49
  | .timeout => 0x54
  | .supervisoryCancel => 0x53
  | .regulatoryCancel => 0x44
  | .selfMatchPrevention => 0x51
  | .systemCancel => 0x5A
  | .crossCancel => 0x43
  | .halted => 0x48
  | .openProtection => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x55 then .userCancel
  else if byte = 0x49 then .iocCancel
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisoryCancel
  else if byte = 0x44 then .regulatoryCancel
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x5A then .systemCancel
  else if byte = 0x43 then .crossCancel
  else if byte = 0x48 then .halted
  else .openProtection

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | userCancel => decide
  | iocCancel => decide
  | timeout => decide
  | supervisoryCancel => decide
  | regulatoryCancel => decide
  | selfMatchPrevention => decide
  | systemCancel => decide
  | crossCancel => decide
  | halted => decide
  | openProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- New Order Accepted Message: 115 bytes -/
structure NewOrderAcceptedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  timeInForce : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  liquidityCode : LiquidityCode
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace NewOrderAcceptedMessage

def encode (message : NewOrderAcceptedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderAcceptedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, capacity, separator12, liquidityCode, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : NewOrderAcceptedMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : NewOrderAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end NewOrderAcceptedMessage

/-- Existing Order Executed Message: 115 bytes -/
structure ExistingOrderExecutedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  matchNumber : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  liquidityCode : LiquidityCode
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace ExistingOrderExecutedMessage

def encode (message : ExistingOrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderExecutedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, matchNumber, separator11, capacity, separator12, liquidityCode, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExistingOrderExecutedMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : ExistingOrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExistingOrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end ExistingOrderExecutedMessage

/-- Existing Order Canceled Message: 115 bytes -/
structure ExistingOrderCanceledMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  timeInForce : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  cancelReason : CancelReason
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace ExistingOrderCanceledMessage

def encode (message : ExistingOrderCanceledMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (CancelReason.encode message.cancelReason
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderCanceledMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, capacity, separator12, cancelReason, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCanceledMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, CancelReason.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : ExistingOrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExistingOrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end ExistingOrderCanceledMessage

/-- Previous Execution Broken Message: 115 bytes -/
structure PreviousExecutionBrokenMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  matchNumber : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  liquidityCode : LiquidityCode
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace PreviousExecutionBrokenMessage

def encode (message : PreviousExecutionBrokenMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (PreviousExecutionBrokenMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, matchNumber, separator11, capacity, separator12, liquidityCode, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : PreviousExecutionBrokenMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : PreviousExecutionBrokenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : PreviousExecutionBrokenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end PreviousExecutionBrokenMessage

/-- Existing Order Replaced Message: 115 bytes -/
structure ExistingOrderReplacedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  timeInForce : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  liquidityCode : LiquidityCode
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace ExistingOrderReplacedMessage

def encode (message : ExistingOrderReplacedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderReplacedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, capacity, separator12, liquidityCode, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExistingOrderReplacedMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : ExistingOrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExistingOrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end ExistingOrderReplacedMessage

/-- Existing Order Cancelled Aiq Message: 115 bytes -/
structure ExistingOrderCancelledAiqMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  timeInForce : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  cancelReason : CancelReason
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace ExistingOrderCancelledAiqMessage

def encode (message : ExistingOrderCancelledAiqMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (CancelReason.encode message.cancelReason
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderCancelledAiqMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, capacity, separator12, cancelReason, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCancelledAiqMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, CancelReason.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : ExistingOrderCancelledAiqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExistingOrderCancelledAiqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end ExistingOrderCancelledAiqMessage

/-- Trade Correction Message: 115 bytes -/
structure TradeCorrectionMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  orderToken : Alpha 15
  separator3 : Alpha 1
  replacedToken : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 8
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 12
  separator10 : Alpha 1
  matchNumber : Alpha 12
  separator11 : Alpha 1
  capacity : Capacity
  separator12 : Alpha 1
  liquidityCode : LiquidityCode
  separator13 : Alpha 1
  clearingCode : ClearingCode
  separator14 : Alpha 1
  referencePrice : Alpha 11
  separator15 : Alpha 1
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator4
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator11
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator12
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator13
    ++ (ClearingCode.encode message.clearingCode
    ++ (Alpha.encode message.separator14
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.separator15
    ++ (ReferencePriceType.encode message.referencePriceType)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (orderToken, bytes) ← Alpha.decode 15 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (referencePrice, bytes) ← Alpha.decode 11 bytes
  let (separator15, bytes) ← Alpha.decode 1 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ separator1, source, separator2, orderToken, separator3, replacedToken, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, matchNumber, separator11, capacity, separator12, liquidityCode, separator13, clearingCode, separator14, referencePrice, separator15, referencePriceType }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | newOrderAcceptedMessage (message : NewOrderAcceptedMessage) -- "A" 0x41
  | existingOrderExecutedMessage (message : ExistingOrderExecutedMessage) -- "E" 0x45
  | existingOrderCanceledMessage (message : ExistingOrderCanceledMessage) -- "X" 0x58
  | previousExecutionBrokenMessage (message : PreviousExecutionBrokenMessage) -- "B" 0x42
  | existingOrderReplacedMessage (message : ExistingOrderReplacedMessage) -- "U" 0x55
  | existingOrderCancelledAiqMessage (message : ExistingOrderCancelledAiqMessage) -- "Y" 0x59
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .newOrderAcceptedMessage _ => 65
  | .existingOrderExecutedMessage _ => 69
  | .existingOrderCanceledMessage _ => 88
  | .previousExecutionBrokenMessage _ => 66
  | .existingOrderReplacedMessage _ => 85
  | .existingOrderCancelledAiqMessage _ => 89
  | .tradeCorrectionMessage _ => 67

def encode : SequencedMessage → List UInt8
  | .newOrderAcceptedMessage message => NewOrderAcceptedMessage.encode message
  | .existingOrderExecutedMessage message => ExistingOrderExecutedMessage.encode message
  | .existingOrderCanceledMessage message => ExistingOrderCanceledMessage.encode message
  | .previousExecutionBrokenMessage message => PreviousExecutionBrokenMessage.encode message
  | .existingOrderReplacedMessage message => ExistingOrderReplacedMessage.encode message
  | .existingOrderCancelledAiqMessage message => ExistingOrderCancelledAiqMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 115 := by
  cases message with
  | newOrderAcceptedMessage inner =>
    simp only [encode, NewOrderAcceptedMessage.encode_length]
    omega
  | existingOrderExecutedMessage inner =>
    simp only [encode, ExistingOrderExecutedMessage.encode_length]
    omega
  | existingOrderCanceledMessage inner =>
    simp only [encode, ExistingOrderCanceledMessage.encode_length]
    omega
  | previousExecutionBrokenMessage inner =>
    simp only [encode, PreviousExecutionBrokenMessage.encode_length]
    omega
  | existingOrderReplacedMessage inner =>
    simp only [encode, ExistingOrderReplacedMessage.encode_length]
    omega
  | existingOrderCancelledAiqMessage inner =>
    simp only [encode, ExistingOrderCancelledAiqMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 65 then (NewOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.newOrderAcceptedMessage message, rest)
  else if tag = 69 then (ExistingOrderExecutedMessage.decode bytes).map fun (message, rest) => (.existingOrderExecutedMessage message, rest)
  else if tag = 88 then (ExistingOrderCanceledMessage.decode bytes).map fun (message, rest) => (.existingOrderCanceledMessage message, rest)
  else if tag = 66 then (PreviousExecutionBrokenMessage.decode bytes).map fun (message, rest) => (.previousExecutionBrokenMessage message, rest)
  else if tag = 85 then (ExistingOrderReplacedMessage.decode bytes).map fun (message, rest) => (.existingOrderReplacedMessage message, rest)
  else if tag = 89 then (ExistingOrderCancelledAiqMessage.decode bytes).map fun (message, rest) => (.existingOrderCancelledAiqMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  timeStamp : Alpha 9
  comma : Alpha 1
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  Alpha.encode message.timeStamp
    ++ (Alpha.encode message.comma
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (timeStamp, bytes) ← Alpha.decode 9 bytes
  let (comma, bytes) ← Alpha.decode 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode messageType bytes
  pure ({ timeStamp, comma, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 126 := by
  unfold encode
  cases message.sequencedMessage with
  | newOrderAcceptedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NewOrderAcceptedMessage.encode_length]
    omega
  | existingOrderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderExecutedMessage.encode_length]
    omega
  | existingOrderCanceledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderCanceledMessage.encode_length]
    omega
  | previousExecutionBrokenMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, PreviousExecutionBrokenMessage.encode_length]
    omega
  | existingOrderReplacedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderReplacedMessage.encode_length]
    omega
  | existingOrderCancelledAiqMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderCancelledAiqMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 126 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Frame -/
structure ServerFrame where
  serverPayload : ServerPayload
  soupLf : BitVec 8
  deriving DecidableEq, Repr

namespace ServerFrame

def encode (message : ServerFrame) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload
    ++ (encodeUInt 1 message.soupLf))

def decode (bytes : List UInt8) : Option (ServerFrame × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  let (soupLf, bytes) ← decodeUInt 1 bytes
  pure ({ serverPayload, soupLf }, bytes)

theorem encode_length_pos (message : ServerFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerFrame) : (encode message).length ≤ 128 := by
  unfold encode
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ServerFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ServerPayload.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ServerFrame

/-- Server Packet -/
structure ServerPacket where
  serverFrame : List ServerFrame
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerFrame.encode message.serverFrame

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverFrame ← decodeAll ServerFrame.decode bytes.length bytes
  pure { serverFrame }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerFrame.encode ServerFrame.decode ServerFrame.decode_encode ServerFrame.encode_length_pos message.serverFrame _ (encodeMany_length_ge ServerFrame.encode ServerFrame.encode_length_pos message.serverFrame), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNsmequitiesDropAsciidropV22Server
