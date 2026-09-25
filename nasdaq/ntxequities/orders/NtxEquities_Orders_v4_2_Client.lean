import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) BX Orders v4.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxequitiesOrdersOuchV42Client

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .sellShort => 0x54
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x41, 0x59, 0x4E, 0x50, 0x49, 0x5A, 0x4D, 0x4F, 0x54, 0x51]

inductive Display where
  | attributablePrice -- Attributable Price
  | anonymousPrice -- Anonymous Price
  | nonDisplay -- Non Display
  | postOnly -- Post Only
  | imbalanceOnly -- Imbalance Only
  | changedToNondisplayed -- Changed To Nondisplayed
  | midPoint -- Mid Point
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovementOrder -- Retail Price Improvement Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .attributablePrice => 0x41
  | .anonymousPrice => 0x59
  | .nonDisplay => 0x4E
  | .postOnly => 0x50
  | .imbalanceOnly => 0x49
  | .changedToNondisplayed => 0x5A
  | .midPoint => 0x4D
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovementOrder => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x41 then .attributablePrice
  else if byte = 0x59 then .anonymousPrice
  else if byte = 0x4E then .nonDisplay
  else if byte = 0x50 then .postOnly
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x5A then .changedToNondisplayed
  else if byte = 0x4D then .midPoint
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else .retailPriceImprovementOrder

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | attributablePrice => decide
  | anonymousPrice => decide
  | nonDisplay => decide
  | postOnly => decide
  | imbalanceOnly => decide
  | changedToNondisplayed => decide
  | midPoint => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovementOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x4F, 0x41, 0x50, 0x52]

inductive Capacity where
  | other -- Other
  | agency -- Agency
  | principal -- Principal
  | riskless -- Riskless
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .other => 0x4F
  | .agency => 0x41
  | .principal => 0x50
  | .riskless => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x4F then .other
  else if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .riskless

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | other => decide
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

/-- Intermarket Sweep Eligibility: one byte code -/
def IntermarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E, 0x79]

inductive IntermarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | tradeat -- Tradeat
  | unlisted (byte : { byte : UInt8 // byte ∉ IntermarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IntermarketSweepEligibility

def toByte : IntermarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .tradeat => 0x79
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IntermarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else if byte = 0x4E then .notEligible
  else .tradeat

def ofByte (byte : UInt8) : IntermarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IntermarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | tradeat => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IntermarketSweepEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IntermarketSweepEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IntermarketSweepEligibility) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IntermarketSweepEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IntermarketSweepEligibility

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4E, 0x4F, 0x43, 0x52]

inductive CrossType where
  | noCross -- No Cross
  | opening -- Opening
  | closing -- Closing
  | retail -- Retail
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .noCross => 0x4E
  | .opening => 0x4F
  | .closing => 0x43
  | .retail => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4E then .noCross
  else if byte = 0x4F then .opening
  else if byte = 0x43 then .closing
  else .retail

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | noCross => decide
  | opening => decide
  | closing => decide
  | retail => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

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

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestPacket

/-- Enter Order Message: 47 bytes -/
structure EnterOrderMessage where
  orderToken : Alpha 14
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  timeInForce : BitVec 32
  firm : Alpha 4
  display : Display
  capacity : Capacity
  intermarketSweepEligibility : IntermarketSweepEligibility
  minimumQuantity : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Alpha.encode message.firm
    ++ (Display.encode message.display
    ++ (Capacity.encode message.capacity
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (CrossType.encode message.crossType)))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ orderToken, buySellIndicator, shares, stock, price, timeInForce, firm, display, capacity, intermarketSweepEligibility, minimumQuantity, crossType }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length, encodeUInt_length, Display.encode_length, Capacity.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CrossType.decode_encode, some_bind]
  rfl

end EnterOrderMessage

/-- Replace Order Message: 46 bytes -/
structure ReplaceOrderMessage where
  existingOrderToken : Alpha 14
  replacementOrderToken : Alpha 14
  shares : BitVec 32
  price : BitVec 32
  timeInForce : BitVec 32
  display : Display
  intermarketSweepEligibility : IntermarketSweepEligibility
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  Alpha.encode message.existingOrderToken
    ++ (Alpha.encode message.replacementOrderToken
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Display.encode message.display
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (encodeUInt 4 message.minimumQuantity)))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (existingOrderToken, bytes) ← Alpha.decode 14 bytes
  let (replacementOrderToken, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ existingOrderToken, replacementOrderToken, shares, price, timeInForce, display, intermarketSweepEligibility, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Display.encode_length, IntermarketSweepEligibility.encode_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 18 bytes -/
structure CancelOrderMessage where
  orderToken : Alpha 14
  shares : BitVec 32
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.shares)

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  pure ({ orderToken, shares }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelOrderMessage

/-- Modify Order Message: 19 bytes -/
structure ModifyOrderMessage where
  orderToken : Alpha 14
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.shares))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  pure ({ orderToken, buySellIndicator, shares }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ModifyOrderMessage

/-- Trade Now Message: 14 bytes -/
structure TradeNowMessage where
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace TradeNowMessage

def encode (message : TradeNowMessage) : List UInt8 :=
  Alpha.encode message.orderToken

def decode (bytes : List UInt8) : Option (TradeNowMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ orderToken }, bytes)

@[simp] theorem encode_length (message : TradeNowMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TradeNowMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeNowMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeNowMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- "U" 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- "X" 0x58
  | modifyOrderMessage (message : ModifyOrderMessage) -- "M" 0x4D
  | tradeNowMessage (message : TradeNowMessage) -- "N" 0x4E
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88
  | .modifyOrderMessage _ => 77
  | .tradeNowMessage _ => 78

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .tradeNowMessage message => TradeNowMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 47 := by
  cases message with
  | enterOrderMessage inner =>
    simp only [encode, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [encode, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | tradeNowMessage inner =>
    simp only [encode, TradeNowMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if tag = 77 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 78 then (TradeNowMessage.decode bytes).map fun (message, rest) => (.tradeNowMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 48 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderMessage.encode_length]
    omega
  | tradeNowMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, TradeNowMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- "R" 0x52
  | logoutRequest (message : LogoutRequest) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 48 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeat.decode bytes).map fun (message, rest) => (.clientHeartbeat message, rest)
  else if tag = 79 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | debugPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
    omega
  | clientHeartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LogoutRequest.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNtxequitiesOrdersOuchV42Client
