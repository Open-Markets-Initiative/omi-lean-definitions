import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Drop v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqBxequitiesDropAsciidropV21

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
  [0x41, 0x52, 0x4A, 0x58, 0x44, 0x46, 0x47, 0x59, 0x53, 0x55, 0x45, 0x50, 0x54, 0x5A, 0x51, 0x6D, 0x6B, 0x6A, 0x72, 0x74, 0x71, 0x37, 0x38, 0x70, 0x4E]

inductive LiquidityCode where
  | addedLiquidity -- Added Liquidity
  | reducedLiquidity -- Reduced Liquidity
  | nondisplayedAndAddedLiquidity -- Nondisplayed And Added Liquidity
  | routed -- Routed
  | dotRouted -- Dot Routed
  | openingTradeOnNyse -- Opening Trade On Nyse
  | onCloseOrderOnNyse -- On Close Order On Nyse
  | reRoutedByNyse -- Re Routed By Nyse
  | oddLotExecutionsOnNyse -- Odd Lot Executions On Nyse
  | addedLiquidityOnNyse -- Added Liquidity On Nyse
  | nyseOther -- Nyse Other
  | routedToPsx -- Routed To Psx
  | openingTradeOnArca -- Opening Trade On Arca
  | onCloseOrderOnArca -- On Close Order On Arca
  | routedToNasdaq -- Routed To Nasdaq
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | rpiRetailPriceImprovingOrderProvidesLiquidity -- Rpi Retail Price Improving Order Provides Liquidity
  | rmoRetailOrderRemovesRpiLiquidity -- Rmo Retail Order Removes Rpi Liquidity
  | rmoRetailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity -- Rmo Retail Order Removes Price Improving Nondisplayed Liquidity Other Than Rpi Liquidity
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity -- Rmo Retail Order Removes Non Rpi Midpoint Liquidity
  | displayedLiquidityaddingOrderImprovesTheNbbo -- Displayed Liquidityadding Order Improves The Nbbo
  | displayedLiquidityaddingOrderSetsTheBxbboWhileJoiningTheNbbo -- Displayed Liquidityadding Order Sets The Bxbbo While Joining The Nbbo
  | removedPriceImprovingNondisplayedLiquidity -- Removed Price Improving Nondisplayed Liquidity
  | passiveMidpointExecution -- Passive Midpoint Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityCode

def toByte : LiquidityCode → UInt8
  | .addedLiquidity => 0x41
  | .reducedLiquidity => 0x52
  | .nondisplayedAndAddedLiquidity => 0x4A
  | .routed => 0x58
  | .dotRouted => 0x44
  | .openingTradeOnNyse => 0x46
  | .onCloseOrderOnNyse => 0x47
  | .reRoutedByNyse => 0x59
  | .oddLotExecutionsOnNyse => 0x53
  | .addedLiquidityOnNyse => 0x55
  | .nyseOther => 0x45
  | .routedToPsx => 0x50
  | .openingTradeOnArca => 0x54
  | .onCloseOrderOnArca => 0x5A
  | .routedToNasdaq => 0x51
  | .removedLiquidityAtAMidpoint => 0x6D
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .rpiRetailPriceImprovingOrderProvidesLiquidity => 0x6A
  | .rmoRetailOrderRemovesRpiLiquidity => 0x72
  | .rmoRetailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => 0x74
  | .rmoRetailOrderRemovesNonRpiMidpointLiquidity => 0x71
  | .displayedLiquidityaddingOrderImprovesTheNbbo => 0x37
  | .displayedLiquidityaddingOrderSetsTheBxbboWhileJoiningTheNbbo => 0x38
  | .removedPriceImprovingNondisplayedLiquidity => 0x70
  | .passiveMidpointExecution => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityCode :=
  if byte = 0x41 then .addedLiquidity
  else if byte = 0x52 then .reducedLiquidity
  else if byte = 0x4A then .nondisplayedAndAddedLiquidity
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dotRouted
  else if byte = 0x46 then .openingTradeOnNyse
  else if byte = 0x47 then .onCloseOrderOnNyse
  else if byte = 0x59 then .reRoutedByNyse
  else if byte = 0x53 then .oddLotExecutionsOnNyse
  else if byte = 0x55 then .addedLiquidityOnNyse
  else if byte = 0x45 then .nyseOther
  else if byte = 0x50 then .routedToPsx
  else if byte = 0x54 then .openingTradeOnArca
  else if byte = 0x5A then .onCloseOrderOnArca
  else if byte = 0x51 then .routedToNasdaq
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else if byte = 0x6B then .addedLiquidityViaAMidpointOrder
  else if byte = 0x6A then .rpiRetailPriceImprovingOrderProvidesLiquidity
  else if byte = 0x72 then .rmoRetailOrderRemovesRpiLiquidity
  else if byte = 0x74 then .rmoRetailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity
  else if byte = 0x71 then .rmoRetailOrderRemovesNonRpiMidpointLiquidity
  else if byte = 0x37 then .displayedLiquidityaddingOrderImprovesTheNbbo
  else if byte = 0x38 then .displayedLiquidityaddingOrderSetsTheBxbboWhileJoiningTheNbbo
  else if byte = 0x70 then .removedPriceImprovingNondisplayedLiquidity
  else .passiveMidpointExecution

def ofByte (byte : UInt8) : LiquidityCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityCode) : ofByte value.toByte = value := by
  cases value with
  | addedLiquidity => decide
  | reducedLiquidity => decide
  | nondisplayedAndAddedLiquidity => decide
  | routed => decide
  | dotRouted => decide
  | openingTradeOnNyse => decide
  | onCloseOrderOnNyse => decide
  | reRoutedByNyse => decide
  | oddLotExecutionsOnNyse => decide
  | addedLiquidityOnNyse => decide
  | nyseOther => decide
  | routedToPsx => decide
  | openingTradeOnArca => decide
  | onCloseOrderOnArca => decide
  | routedToNasdaq => decide
  | removedLiquidityAtAMidpoint => decide
  | addedLiquidityViaAMidpointOrder => decide
  | rpiRetailPriceImprovingOrderProvidesLiquidity => decide
  | rmoRetailOrderRemovesRpiLiquidity => decide
  | rmoRetailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => decide
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity => decide
  | displayedLiquidityaddingOrderImprovesTheNbbo => decide
  | displayedLiquidityaddingOrderSetsTheBxbboWhileJoiningTheNbbo => decide
  | removedPriceImprovingNondisplayedLiquidity => decide
  | passiveMidpointExecution => decide
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

/-- New Order Accepted Message: 99 bytes -/
structure NewOrderAcceptedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  replacedToken : Alpha 10
  separator5 : Alpha 1
  buySell : BuySell
  separator6 : Alpha 1
  shares : Alpha 6
  separator7 : Alpha 1
  stock : Alpha 6
  separator8 : Alpha 1
  price : Alpha 11
  separator9 : Alpha 1
  firm : Alpha 4
  separator10 : Alpha 1
  reference : Alpha 12
  separator11 : Alpha 1
  timeInForce : Alpha 12
  separator12 : Alpha 1
  capacity : Capacity
  separator13 : Alpha 1
  liquidityCode : LiquidityCode
  separator14 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace NewOrderAcceptedMessage

def encode (message : NewOrderAcceptedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator5
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator11
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator12
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator13
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator14
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderAcceptedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityCode, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : NewOrderAcceptedMessage) : (encode message).length = 99 := by
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

/-- Existing Order Executed Message: 99 bytes -/
structure ExistingOrderExecutedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  replacedToken : Alpha 10
  separator5 : Alpha 1
  buySell : BuySell
  separator6 : Alpha 1
  shares : Alpha 6
  separator7 : Alpha 1
  stock : Alpha 6
  separator8 : Alpha 1
  price : Alpha 11
  separator9 : Alpha 1
  firm : Alpha 4
  separator10 : Alpha 1
  reference : Alpha 12
  separator11 : Alpha 1
  matchNumber : Alpha 12
  separator12 : Alpha 1
  capacity : Capacity
  separator13 : Alpha 1
  liquidityCode : LiquidityCode
  separator14 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace ExistingOrderExecutedMessage

def encode (message : ExistingOrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator5
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator11
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator12
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator13
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator14
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderExecutedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, matchNumber, separator12, capacity, separator13, liquidityCode, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderExecutedMessage) : (encode message).length = 99 := by
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

/-- Existing Order Canceled Message: 99 bytes -/
structure ExistingOrderCanceledMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  replacedToken : Alpha 10
  separator5 : Alpha 1
  buySell : BuySell
  separator6 : Alpha 1
  shares : Alpha 6
  separator7 : Alpha 1
  stock : Alpha 6
  separator8 : Alpha 1
  price : Alpha 11
  separator9 : Alpha 1
  firm : Alpha 4
  separator10 : Alpha 1
  reference : Alpha 12
  separator11 : Alpha 1
  timeInForce : Alpha 12
  separator12 : Alpha 1
  capacity : Capacity
  separator13 : Alpha 1
  liquidityCode : LiquidityCode
  separator14 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace ExistingOrderCanceledMessage

def encode (message : ExistingOrderCanceledMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator5
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator11
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator12
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator13
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator14
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderCanceledMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityCode, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCanceledMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

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

end ExistingOrderCanceledMessage

/-- Previous Execution Broken Message: 99 bytes -/
structure PreviousExecutionBrokenMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  replacedToken : Alpha 10
  separator5 : Alpha 1
  buySell : BuySell
  separator6 : Alpha 1
  shares : Alpha 6
  separator7 : Alpha 1
  stock : Alpha 6
  separator8 : Alpha 1
  price : Alpha 11
  separator9 : Alpha 1
  firm : Alpha 4
  separator10 : Alpha 1
  reference : Alpha 12
  separator11 : Alpha 1
  matchNumber : Alpha 12
  separator12 : Alpha 1
  capacity : Capacity
  separator13 : Alpha 1
  liquidityCode : LiquidityCode
  separator14 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace PreviousExecutionBrokenMessage

def encode (message : PreviousExecutionBrokenMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator5
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator11
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.separator12
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator13
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator14
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (PreviousExecutionBrokenMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, matchNumber, separator12, capacity, separator13, liquidityCode, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : PreviousExecutionBrokenMessage) : (encode message).length = 99 := by
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

/-- Existing Order Replaced Message: 99 bytes -/
structure ExistingOrderReplacedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  replacedToken : Alpha 10
  separator5 : Alpha 1
  buySell : BuySell
  separator6 : Alpha 1
  shares : Alpha 6
  separator7 : Alpha 1
  stock : Alpha 6
  separator8 : Alpha 1
  price : Alpha 11
  separator9 : Alpha 1
  firm : Alpha 4
  separator10 : Alpha 1
  reference : Alpha 12
  separator11 : Alpha 1
  timeInForce : Alpha 12
  separator12 : Alpha 1
  capacity : Capacity
  separator13 : Alpha 1
  liquidityCode : LiquidityCode
  separator14 : Alpha 1
  clearingCode : ClearingCode
  deriving DecidableEq, Repr

namespace ExistingOrderReplacedMessage

def encode (message : ExistingOrderReplacedMessage) : List UInt8 :=
  Alpha.encode message.separator1
    ++ (Alpha.encode message.source
    ++ (Alpha.encode message.separator2
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.separator3
    ++ (Alpha.encode message.token
    ++ (Alpha.encode message.separator4
    ++ (Alpha.encode message.replacedToken
    ++ (Alpha.encode message.separator5
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.separator6
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.separator7
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.separator8
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.separator9
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.separator10
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.separator11
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.separator12
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.separator13
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator14
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExistingOrderReplacedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (replacedToken, bytes) ← Alpha.decode 10 bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 12 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 12 bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (separator13, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityCode, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderReplacedMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

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

end ExistingOrderReplacedMessage

/-- Any Message, selected by Message Type -/
inductive Message where
  | newOrderAcceptedMessage (message : NewOrderAcceptedMessage) -- "A" 0x41
  | existingOrderExecutedMessage (message : ExistingOrderExecutedMessage) -- "E" 0x45
  | existingOrderCanceledMessage (message : ExistingOrderCanceledMessage) -- "X" 0x58
  | previousExecutionBrokenMessage (message : PreviousExecutionBrokenMessage) -- "B" 0x42
  | existingOrderReplacedMessage (message : ExistingOrderReplacedMessage) -- "U" 0x55
  deriving DecidableEq, Repr

namespace Message

/-- The Message Type each message is sent under -/
def tag : Message → BitVec 8
  | .newOrderAcceptedMessage _ => 65
  | .existingOrderExecutedMessage _ => 69
  | .existingOrderCanceledMessage _ => 88
  | .previousExecutionBrokenMessage _ => 66
  | .existingOrderReplacedMessage _ => 85

def encode : Message → List UInt8
  | .newOrderAcceptedMessage message => NewOrderAcceptedMessage.encode message
  | .existingOrderExecutedMessage message => ExistingOrderExecutedMessage.encode message
  | .existingOrderCanceledMessage message => ExistingOrderCanceledMessage.encode message
  | .previousExecutionBrokenMessage message => PreviousExecutionBrokenMessage.encode message
  | .existingOrderReplacedMessage message => ExistingOrderReplacedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 99 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) :=
  if tag = 65 then (NewOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.newOrderAcceptedMessage message, rest)
  else if tag = 69 then (ExistingOrderExecutedMessage.decode bytes).map fun (message, rest) => (.existingOrderExecutedMessage message, rest)
  else if tag = 88 then (ExistingOrderCanceledMessage.decode bytes).map fun (message, rest) => (.existingOrderCanceledMessage message, rest)
  else if tag = 66 then (PreviousExecutionBrokenMessage.decode bytes).map fun (message, rest) => (.previousExecutionBrokenMessage message, rest)
  else if tag = 85 then (ExistingOrderReplacedMessage.decode bytes).map fun (message, rest) => (.existingOrderReplacedMessage message, rest)
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
theorem encode_length_le (message : Line) : (encode message).length ≤ 112 := by
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
  | existingOrderReplacedMessage inner =>
    simp only [Message.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExistingOrderReplacedMessage.encode_length]
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

end Omi.NasdaqBxequitiesDropAsciidropV21
