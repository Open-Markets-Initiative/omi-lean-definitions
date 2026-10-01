import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Drop v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesDropAsciidropV10

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
  [0x41, 0x52, 0x58, 0x44, 0x46, 0x47, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x4A, 0x59, 0x53, 0x55, 0x42, 0x45, 0x50, 0x54, 0x5A, 0x57, 0x6D, 0x6B, 0x30, 0x37, 0x38, 0x64, 0x65, 0x66, 0x6A, 0x72, 0x74, 0x34, 0x35, 0x36, 0x67]

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
  | addedDisplayedLiquidityInASelectSymbol -- Added Displayed Liquidity In A Select Symbol
  | addedNondisplayedLiquidityInASelectSymbol -- Added Nondisplayed Liquidity In A Select Symbol
  | liquidityRemovingOrderInASelectSymbol -- Liquidity Removing Order In A Select Symbol
  | addedNondisplayedMidpointLiquidityInASelectSymbol -- Added Nondisplayed Midpoint Liquidity In A Select Symbol
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
  | .addedDisplayedLiquidityInASelectSymbol => 0x34
  | .addedNondisplayedLiquidityInASelectSymbol => 0x35
  | .liquidityRemovingOrderInASelectSymbol => 0x36
  | .addedNondisplayedMidpointLiquidityInASelectSymbol => 0x67
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
  else if byte = 0x34 then .addedDisplayedLiquidityInASelectSymbol
  else if byte = 0x35 then .addedNondisplayedLiquidityInASelectSymbol
  else if byte = 0x36 then .liquidityRemovingOrderInASelectSymbol
  else .addedNondisplayedMidpointLiquidityInASelectSymbol

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
  | addedDisplayedLiquidityInASelectSymbol => decide
  | addedNondisplayedLiquidityInASelectSymbol => decide
  | liquidityRemovingOrderInASelectSymbol => decide
  | addedNondisplayedMidpointLiquidityInASelectSymbol => decide
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

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x5A, 0x43]

inductive CancelReason where
  | userCancel -- User Cancel
  | iocCancel -- Ioc Cancel
  | timeout -- Timeout
  | supervisoryCancel -- Supervisory Cancel
  | regulatoryCancel -- Regulatory Cancel
  | selfMatchPrevention -- Self Match Prevention
  | systemCancel -- System Cancel
  | crossCancel -- Cross Cancel
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
  else .crossCancel

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

/-- New Order Accepted Message: 93 bytes -/
structure NewOrderAcceptedMessage where
  source : Alpha 6
  separator1 : Alpha 1
  user : Alpha 4
  separator2 : Alpha 1
  token : Alpha 10
  separator3 : Alpha 1
  buySell : BuySell
  separator4 : Alpha 1
  shares : Alpha 9
  separator5 : Alpha 1
  stock : Alpha 6
  separator6 : Alpha 1
  price : Alpha 20
  separator7 : Alpha 1
  firm : Alpha 4
  separator8 : Alpha 1
  reference : Alpha 9
  separator9 : Alpha 1
  timeInForce : Alpha 9
  separator10 : Alpha 1
  capacity : Capacity
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace NewOrderAcceptedMessage

def encode (message : NewOrderAcceptedMessage) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.separator1
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator3
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator10
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator11
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderAcceptedMessage × List UInt8) := do
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ source, separator1, user, separator2, token, separator3, buySell, separator4, shares, separator5, stock, separator6, price, separator7, firm, separator8, reference, separator9, timeInForce, separator10, capacity, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : NewOrderAcceptedMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

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
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end NewOrderAcceptedMessage

/-- Existing Order Executed Message: 93 bytes -/
structure ExistingOrderExecutedMessage where
  source : Alpha 6
  separator1 : Alpha 1
  user : Alpha 4
  separator2 : Alpha 1
  token : Alpha 10
  separator3 : Alpha 1
  buySell : BuySell
  separator4 : Alpha 1
  shares : Alpha 9
  separator5 : Alpha 1
  stock : Alpha 6
  separator6 : Alpha 1
  price : Alpha 20
  separator7 : Alpha 1
  firm : Alpha 4
  separator8 : Alpha 1
  reference : Alpha 9
  separator9 : Alpha 1
  matchNumber : Alpha 9
  separator10 : Alpha 1
  capacity : Capacity
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace ExistingOrderExecutedMessage

def encode (message : ExistingOrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.separator1
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator3
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator10
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator11
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderExecutedMessage × List UInt8) := do
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ source, separator1, user, separator2, token, separator3, buySell, separator4, shares, separator5, stock, separator6, price, separator7, firm, separator8, reference, separator9, matchNumber, separator10, capacity, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderExecutedMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

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
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end ExistingOrderExecutedMessage

/-- Existing Order Canceled Message: 93 bytes -/
structure ExistingOrderCanceledMessage where
  source : Alpha 6
  separator1 : Alpha 1
  user : Alpha 4
  separator2 : Alpha 1
  token : Alpha 10
  separator3 : Alpha 1
  buySell : BuySell
  separator4 : Alpha 1
  shares : Alpha 9
  separator5 : Alpha 1
  stock : Alpha 6
  separator6 : Alpha 1
  price : Alpha 20
  separator7 : Alpha 1
  firm : Alpha 4
  separator8 : Alpha 1
  reference : Alpha 9
  separator9 : Alpha 1
  timeInForce : Alpha 9
  separator10 : Alpha 1
  capacity : Capacity
  separator11 : Alpha 1
  cancelReason : CancelReason
  separator12 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace ExistingOrderCanceledMessage

def encode (message : ExistingOrderCanceledMessage) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.separator1
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator3
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator10
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator11
    ++ (CancelReason.encode message.cancelReason
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderCanceledMessage × List UInt8) := do
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ source, separator1, user, separator2, token, separator3, buySell, separator4, shares, separator5, stock, separator6, price, separator7, firm, separator8, reference, separator9, timeInForce, separator10, capacity, separator11, cancelReason, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCanceledMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, CancelReason.encode_length, ClearingCode.encode_length]

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
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end ExistingOrderCanceledMessage

/-- Previous Execution Broken Message: 93 bytes -/
structure PreviousExecutionBrokenMessage where
  source : Alpha 6
  separator1 : Alpha 1
  user : Alpha 4
  separator2 : Alpha 1
  token : Alpha 10
  separator3 : Alpha 1
  buySell : BuySell
  separator4 : Alpha 1
  shares : Alpha 9
  separator5 : Alpha 1
  stock : Alpha 6
  separator6 : Alpha 1
  price : Alpha 20
  separator7 : Alpha 1
  firm : Alpha 4
  separator8 : Alpha 1
  reference : Alpha 9
  separator9 : Alpha 1
  matchNumber : Alpha 9
  separator10 : Alpha 1
  capacity : Capacity
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace PreviousExecutionBrokenMessage

def encode (message : PreviousExecutionBrokenMessage) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.separator1
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator3
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator5
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator10
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator11
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (PreviousExecutionBrokenMessage × List UInt8) := do
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ source, separator1, user, separator2, token, separator3, buySell, separator4, shares, separator5, stock, separator6, price, separator7, firm, separator8, reference, separator9, matchNumber, separator10, capacity, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : PreviousExecutionBrokenMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

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
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end PreviousExecutionBrokenMessage

/-- Any Message, selected by Message Type -/
inductive Message where
  | newOrderAcceptedMessage (message : NewOrderAcceptedMessage) -- "A" 0x41
  | existingOrderExecutedMessage (message : ExistingOrderExecutedMessage) -- "E" 0x45
  | existingOrderCanceledMessage (message : ExistingOrderCanceledMessage) -- "X" 0x58
  | previousExecutionBrokenMessage (message : PreviousExecutionBrokenMessage) -- "B" 0x42
  deriving DecidableEq, Repr

namespace Message

/-- The Message Type each message is sent under -/
def tag : Message → BitVec 8
  | .newOrderAcceptedMessage _ => 65
  | .existingOrderExecutedMessage _ => 69
  | .existingOrderCanceledMessage _ => 88
  | .previousExecutionBrokenMessage _ => 66

def encode : Message → List UInt8
  | .newOrderAcceptedMessage message => NewOrderAcceptedMessage.encode message
  | .existingOrderExecutedMessage message => ExistingOrderExecutedMessage.encode message
  | .existingOrderCanceledMessage message => ExistingOrderCanceledMessage.encode message
  | .previousExecutionBrokenMessage message => PreviousExecutionBrokenMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 93 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) :=
  if tag = 65 then (NewOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.newOrderAcceptedMessage message, rest)
  else if tag = 69 then (ExistingOrderExecutedMessage.decode bytes).map fun (message, rest) => (.existingOrderExecutedMessage message, rest)
  else if tag = 88 then (ExistingOrderCanceledMessage.decode bytes).map fun (message, rest) => (.existingOrderCanceledMessage message, rest)
  else if tag = 66 then (PreviousExecutionBrokenMessage.decode bytes).map fun (message, rest) => (.previousExecutionBrokenMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Message

/-- Line -/
structure Line where
  timeStamp : Alpha 9
  comma : Alpha 1
  message : Message
  cr : BitVec 8
  lf : BitVec 8
  deriving DecidableEq, Repr

namespace Line

def encode (message : Line) : List UInt8 :=
  Alpha.encode message.timeStamp
    ++ (Alpha.encode message.comma
    ++ (encodeUInt 1 (Message.tag message.message)
    ++ (Message.encode message.message
    ++ (encodeUInt 1 message.cr
    ++ (encodeUInt 1 message.lf)))))

def decode (bytes : List UInt8) : Option (Line × List UInt8) := do
  let (timeStamp, bytes) ← Alpha.decode 9 bytes
  let (comma, bytes) ← Alpha.decode 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (message, bytes) ← Message.decode messageType bytes
  let (cr, bytes) ← decodeUInt 1 bytes
  let (lf, bytes) ← decodeUInt 1 bytes
  pure ({ timeStamp, comma, message, cr, lf }, bytes)

theorem encode_length_pos (message : Line) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Line) : (encode message).length ≤ 106 := by
  unfold encode
  cases message.message with
  | newOrderAcceptedMessage inner =>
    simp only [Message.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NewOrderAcceptedMessage.encode_length]
    omega
  | existingOrderExecutedMessage inner =>
    simp only [Message.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderExecutedMessage.encode_length]
    omega
  | existingOrderCanceledMessage inner =>
    simp only [Message.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderCanceledMessage.encode_length]
    omega
  | previousExecutionBrokenMessage inner =>
    simp only [Message.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, PreviousExecutionBrokenMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Line) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Message.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Line

end Omi.NasdaqNsmequitiesDropAsciidropV10
