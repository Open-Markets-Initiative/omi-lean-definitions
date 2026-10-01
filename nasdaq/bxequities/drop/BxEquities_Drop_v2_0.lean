import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Drop v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqBxequitiesDropAsciidropV20

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

/-- Liquidity Code: one byte code -/
def LiquidityCode.codes : List UInt8 :=
  [0x41, 0x52, 0x58, 0x44, 0x46, 0x47, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x49, 0x4A, 0x59, 0x53, 0x55, 0x42, 0x45, 0x50, 0x54, 0x5A, 0x6D, 0x6B]

inductive LiquidityCode where
  | added -- Added
  | removed -- Removed
  | routed -- Routed
  | dot -- Dot
  | addedOrOpeningTradeOnNyse -- Added Or Opening Trade On Nyse
  | oddLotOrOnCloseOrderOnNyse -- Odd Lot Or On Close Order On Nyse
  | openingCrossBillable -- Opening Cross Billable
  | openingCrossNonbillable -- Opening Cross Nonbillable
  | closingCrossBillable -- Closing Cross Billable
  | closingCrossNonbillable -- Closing Cross Nonbillable
  | haltIpoCrossBillable -- Halt Ipo Cross Billable
  | haltIpoCrossNonbillable -- Halt Ipo Cross Nonbillable
  | intradayAndPostmarketCrosses -- Intraday And Postmarket Crosses
  | nondisplayedAddingLiquidity -- Nondisplayed Adding Liquidity
  | reRoutedByNyse -- Re Routed By Nyse
  | oddLotExecutionOnNyse -- Odd Lot Execution On Nyse
  | addedLiquidityOnNyse -- Added Liquidity On Nyse
  | routedToBx -- Routed To Bx
  | nyseOther -- Nyse Other
  | routedToPsx -- Routed To Psx
  | openingTradeOnArca -- Opening Trade On Arca
  | onCloseOrderOnArca -- On Close Order On Arca
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityCode

def toByte : LiquidityCode → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .routed => 0x58
  | .dot => 0x44
  | .addedOrOpeningTradeOnNyse => 0x46
  | .oddLotOrOnCloseOrderOnNyse => 0x47
  | .openingCrossBillable => 0x4F
  | .openingCrossNonbillable => 0x4D
  | .closingCrossBillable => 0x43
  | .closingCrossNonbillable => 0x4C
  | .haltIpoCrossBillable => 0x48
  | .haltIpoCrossNonbillable => 0x4B
  | .intradayAndPostmarketCrosses => 0x49
  | .nondisplayedAddingLiquidity => 0x4A
  | .reRoutedByNyse => 0x59
  | .oddLotExecutionOnNyse => 0x53
  | .addedLiquidityOnNyse => 0x55
  | .routedToBx => 0x42
  | .nyseOther => 0x45
  | .routedToPsx => 0x50
  | .openingTradeOnArca => 0x54
  | .onCloseOrderOnArca => 0x5A
  | .removedLiquidityAtAMidpoint => 0x6D
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityCode :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dot
  else if byte = 0x46 then .addedOrOpeningTradeOnNyse
  else if byte = 0x47 then .oddLotOrOnCloseOrderOnNyse
  else if byte = 0x4F then .openingCrossBillable
  else if byte = 0x4D then .openingCrossNonbillable
  else if byte = 0x43 then .closingCrossBillable
  else if byte = 0x4C then .closingCrossNonbillable
  else if byte = 0x48 then .haltIpoCrossBillable
  else if byte = 0x4B then .haltIpoCrossNonbillable
  else if byte = 0x49 then .intradayAndPostmarketCrosses
  else if byte = 0x4A then .nondisplayedAddingLiquidity
  else if byte = 0x59 then .reRoutedByNyse
  else if byte = 0x53 then .oddLotExecutionOnNyse
  else if byte = 0x55 then .addedLiquidityOnNyse
  else if byte = 0x42 then .routedToBx
  else if byte = 0x45 then .nyseOther
  else if byte = 0x50 then .routedToPsx
  else if byte = 0x54 then .openingTradeOnArca
  else if byte = 0x5A then .onCloseOrderOnArca
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else .addedLiquidityViaAMidpointOrder

def ofByte (byte : UInt8) : LiquidityCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityCode) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | routed => decide
  | dot => decide
  | addedOrOpeningTradeOnNyse => decide
  | oddLotOrOnCloseOrderOnNyse => decide
  | openingCrossBillable => decide
  | openingCrossNonbillable => decide
  | closingCrossBillable => decide
  | closingCrossNonbillable => decide
  | haltIpoCrossBillable => decide
  | haltIpoCrossNonbillable => decide
  | intradayAndPostmarketCrosses => decide
  | nondisplayedAddingLiquidity => decide
  | reRoutedByNyse => decide
  | oddLotExecutionOnNyse => decide
  | addedLiquidityOnNyse => decide
  | routedToBx => decide
  | nyseOther => decide
  | routedToPsx => decide
  | openingTradeOnArca => decide
  | onCloseOrderOnArca => decide
  | removedLiquidityAtAMidpoint => decide
  | addedLiquidityViaAMidpointOrder => decide
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

/-- New Order Accepted Message: 80 bytes -/
structure NewOrderAcceptedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 6
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 9
  separator10 : Alpha 1
  timeInForce : Alpha 9
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
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
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderAcceptedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 9 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : NewOrderAcceptedMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

theorem encode_length_pos (message : NewOrderAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end NewOrderAcceptedMessage

/-- Existing Order Executed Message: 80 bytes -/
structure ExistingOrderExecutedMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 6
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 9
  separator10 : Alpha 1
  matchNumber : Alpha 9
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
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
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExistingOrderExecutedMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, matchNumber, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderExecutedMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

theorem encode_length_pos (message : ExistingOrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end ExistingOrderExecutedMessage

/-- Existing Order Canceled Message: 80 bytes -/
structure ExistingOrderCanceledMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 6
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 9
  separator10 : Alpha 1
  timeInForce : Alpha 9
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
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
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExistingOrderCanceledMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← Alpha.decode 9 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, timeInForce, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCanceledMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

theorem encode_length_pos (message : ExistingOrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, LiquidityCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end ExistingOrderCanceledMessage

/-- Previous Execution Broken Message: 80 bytes -/
structure PreviousExecutionBrokenMessage where
  separator1 : Alpha 1
  source : Alpha 6
  separator2 : Alpha 1
  user : Alpha 4
  separator3 : Alpha 1
  token : Alpha 10
  separator4 : Alpha 1
  buySell : BuySell
  separator5 : Alpha 1
  shares : Alpha 6
  separator6 : Alpha 1
  stock : Alpha 6
  separator7 : Alpha 1
  price : Alpha 11
  separator8 : Alpha 1
  firm : Alpha 4
  separator9 : Alpha 1
  reference : Alpha 9
  separator10 : Alpha 1
  matchNumber : Alpha 9
  separator11 : Alpha 1
  liquidityCode : LiquidityCode
  separator12 : Alpha 1
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
    ++ (LiquidityCode.encode message.liquidityCode
    ++ (Alpha.encode message.separator12
    ++ (ClearingCode.encode message.clearingCode)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (PreviousExecutionBrokenMessage × List UInt8) := do
  let (separator1, bytes) ← Alpha.decode 1 bytes
  let (source, bytes) ← Alpha.decode 6 bytes
  let (separator2, bytes) ← Alpha.decode 1 bytes
  let (user, bytes) ← Alpha.decode 4 bytes
  let (separator3, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 10 bytes
  let (separator4, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (separator5, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (separator6, bytes) ← Alpha.decode 1 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (separator7, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← Alpha.decode 11 bytes
  let (separator8, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (separator9, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 9 bytes
  let (separator10, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (separator11, bytes) ← Alpha.decode 1 bytes
  let (liquidityCode, bytes) ← LiquidityCode.decode bytes
  let (separator12, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, buySell, separator5, shares, separator6, stock, separator7, price, separator8, firm, separator9, reference, separator10, matchNumber, separator11, liquidityCode, separator12, clearingCode }, bytes)

@[simp] theorem encode_length (message : PreviousExecutionBrokenMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, LiquidityCode.encode_length, ClearingCode.encode_length]

theorem encode_length_pos (message : PreviousExecutionBrokenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
theorem encode_length_le (message : Message) : (encode message).length ≤ 80 := by
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
theorem encode_length_le (message : Line) : (encode message).length ≤ 93 := by
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

end Omi.NasdaqBxequitiesDropAsciidropV20
