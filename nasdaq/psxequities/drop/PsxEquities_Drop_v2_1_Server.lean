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

namespace Omi.NasdaqPsxequitiesDropAsciidropV21Server

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

/-- Liquidity Flag: one byte code -/
def LiquidityFlag.codes : List UInt8 :=
  [0x41, 0x52, 0x56, 0x58, 0x44, 0x46, 0x47, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x4A, 0x59, 0x53, 0x55, 0x42, 0x45, 0x50, 0x54, 0x5A, 0x6D, 0x6B]

inductive LiquidityFlag where
  | added -- Added
  | removed -- Removed
  | displayedAddedLiquidityWithOriginalOrderSizeOfGreaterThanOrEqualTo2000Shares -- Displayed Added Liquidity With Original Order Size Of Greater Than Or Equal To 2000 Shares
  | routed -- Routed
  | dot -- Dot
  | addedOrOpeningTradeOnNyse -- Added Or Opening Trade On Nyse
  | oddLotOrOnCloseOrderOnNyse -- Odd Lot Or On Close Order On Nyse
  | openingCross -- Opening Cross
  | openingCrossImbalanceonly -- Opening Cross Imbalanceonly
  | closingCross -- Closing Cross
  | closingCrossImbalanceonly -- Closing Cross Imbalanceonly
  | haltIpoCross -- Halt Ipo Cross
  | haltCross -- Halt Cross
  | nondisplayedAndAddedLiquidity -- Nondisplayed And Added Liquidity
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
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityFlag

def toByte : LiquidityFlag → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .displayedAddedLiquidityWithOriginalOrderSizeOfGreaterThanOrEqualTo2000Shares => 0x56
  | .routed => 0x58
  | .dot => 0x44
  | .addedOrOpeningTradeOnNyse => 0x46
  | .oddLotOrOnCloseOrderOnNyse => 0x47
  | .openingCross => 0x4F
  | .openingCrossImbalanceonly => 0x4D
  | .closingCross => 0x43
  | .closingCrossImbalanceonly => 0x4C
  | .haltIpoCross => 0x48
  | .haltCross => 0x4B
  | .nondisplayedAndAddedLiquidity => 0x4A
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
def listed (byte : UInt8) : LiquidityFlag :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x56 then .displayedAddedLiquidityWithOriginalOrderSizeOfGreaterThanOrEqualTo2000Shares
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dot
  else if byte = 0x46 then .addedOrOpeningTradeOnNyse
  else if byte = 0x47 then .oddLotOrOnCloseOrderOnNyse
  else if byte = 0x4F then .openingCross
  else if byte = 0x4D then .openingCrossImbalanceonly
  else if byte = 0x43 then .closingCross
  else if byte = 0x4C then .closingCrossImbalanceonly
  else if byte = 0x48 then .haltIpoCross
  else if byte = 0x4B then .haltCross
  else if byte = 0x4A then .nondisplayedAndAddedLiquidity
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

def ofByte (byte : UInt8) : LiquidityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityFlag) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | displayedAddedLiquidityWithOriginalOrderSizeOfGreaterThanOrEqualTo2000Shares => decide
  | routed => decide
  | dot => decide
  | addedOrOpeningTradeOnNyse => decide
  | oddLotOrOnCloseOrderOnNyse => decide
  | openingCross => decide
  | openingCrossImbalanceonly => decide
  | closingCross => decide
  | closingCrossImbalanceonly => decide
  | haltIpoCross => decide
  | haltCross => decide
  | nondisplayedAndAddedLiquidity => decide
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

def encode (value : LiquidityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityFlag

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
  liquidityFlag : LiquidityFlag
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
    ++ (LiquidityFlag.encode message.liquidityFlag
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
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityFlag, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : NewOrderAcceptedMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityFlag.encode_length, ClearingCode.encode_length]

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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
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
  liquidityFlag : LiquidityFlag
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
    ++ (LiquidityFlag.encode message.liquidityFlag
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
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, matchNumber, separator12, capacity, separator13, liquidityFlag, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderExecutedMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityFlag.encode_length, ClearingCode.encode_length]

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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
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
  liquidityFlag : LiquidityFlag
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
    ++ (LiquidityFlag.encode message.liquidityFlag
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
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityFlag, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderCanceledMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityFlag.encode_length, ClearingCode.encode_length]

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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
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
  liquidityFlag : LiquidityFlag
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
    ++ (LiquidityFlag.encode message.liquidityFlag
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
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, matchNumber, separator12, capacity, separator13, liquidityFlag, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : PreviousExecutionBrokenMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityFlag.encode_length, ClearingCode.encode_length]

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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
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
  liquidityFlag : LiquidityFlag
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
    ++ (LiquidityFlag.encode message.liquidityFlag
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
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (separator14, bytes) ← Alpha.decode 1 bytes
  let (clearingCode, bytes) ← ClearingCode.decode bytes
  pure ({ separator1, source, separator2, user, separator3, token, separator4, replacedToken, separator5, buySell, separator6, shares, separator7, stock, separator8, price, separator9, firm, separator10, reference, separator11, timeInForce, separator12, capacity, separator13, liquidityFlag, separator14, clearingCode }, bytes)

@[simp] theorem encode_length (message : ExistingOrderReplacedMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySell.encode_length, Capacity.encode_length, LiquidityFlag.encode_length, ClearingCode.encode_length]

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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClearingCode.decode_encode, some_bind]
  rfl

end ExistingOrderReplacedMessage

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | newOrderAcceptedMessage (message : NewOrderAcceptedMessage) -- "A" 0x41
  | existingOrderExecutedMessage (message : ExistingOrderExecutedMessage) -- "E" 0x45
  | existingOrderCanceledMessage (message : ExistingOrderCanceledMessage) -- "X" 0x58
  | previousExecutionBrokenMessage (message : PreviousExecutionBrokenMessage) -- "B" 0x42
  | existingOrderReplacedMessage (message : ExistingOrderReplacedMessage) -- "U" 0x55
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .newOrderAcceptedMessage _ => 65
  | .existingOrderExecutedMessage _ => 69
  | .existingOrderCanceledMessage _ => 88
  | .previousExecutionBrokenMessage _ => 66
  | .existingOrderReplacedMessage _ => 85

def encode : SequencedMessage → List UInt8
  | .newOrderAcceptedMessage message => NewOrderAcceptedMessage.encode message
  | .existingOrderExecutedMessage message => ExistingOrderExecutedMessage.encode message
  | .existingOrderCanceledMessage message => ExistingOrderCanceledMessage.encode message
  | .previousExecutionBrokenMessage message => PreviousExecutionBrokenMessage.encode message
  | .existingOrderReplacedMessage message => ExistingOrderReplacedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 99 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 65 then (NewOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.newOrderAcceptedMessage message, rest)
  else if tag = 69 then (ExistingOrderExecutedMessage.decode bytes).map fun (message, rest) => (.existingOrderExecutedMessage message, rest)
  else if tag = 88 then (ExistingOrderCanceledMessage.decode bytes).map fun (message, rest) => (.existingOrderCanceledMessage message, rest)
  else if tag = 66 then (PreviousExecutionBrokenMessage.decode bytes).map fun (message, rest) => (.previousExecutionBrokenMessage message, rest)
  else if tag = 85 then (ExistingOrderReplacedMessage.decode bytes).map fun (message, rest) => (.existingOrderReplacedMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 110 := by
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 110 := by
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
theorem encode_length_le (message : ServerFrame) : (encode message).length ≤ 112 := by
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

end Omi.NasdaqPsxequitiesDropAsciidropV21Server
