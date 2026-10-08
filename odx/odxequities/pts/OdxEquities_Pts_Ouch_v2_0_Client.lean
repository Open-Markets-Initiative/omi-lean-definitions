import Wire

/-!
# Osaka Digital Exchange Proprietary Trading System v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OdxOdxequitiesPtsOuchV20Client

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | shortSell -- Short Sell
  | shortSellExempt -- Short Sell Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .shortSell => 0x54
  | .shortSellExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .shortSell
  else .shortSellExempt

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | shortSell => decide
  | shortSellExempt => decide
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
  [0x50]

inductive Display where
  | postonly -- Postonly
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .postonly => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Display :=
  .postonly

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | postonly => decide
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
  [0x41, 0x50]

inductive Capacity where
  | agency -- Agency
  | principal -- Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x41 then .agency
  else .principal

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
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

/-- Order Classification: one byte code -/
def OrderClassification.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36]

inductive OrderClassification where
  | nonHft -- Non Hft
  | hftMarketMakingStrategy -- Hft Market Making Strategy
  | hftArbitrageStrategy -- Hft Arbitrage Strategy
  | hftDirectionalStrategy -- Hft Directional Strategy
  | hftOtherStrategy -- Hft Other Strategy
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderClassification

def toByte : OrderClassification → UInt8
  | .nonHft => 0x31
  | .hftMarketMakingStrategy => 0x33
  | .hftArbitrageStrategy => 0x34
  | .hftDirectionalStrategy => 0x35
  | .hftOtherStrategy => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderClassification :=
  if byte = 0x31 then .nonHft
  else if byte = 0x33 then .hftMarketMakingStrategy
  else if byte = 0x34 then .hftArbitrageStrategy
  else if byte = 0x35 then .hftDirectionalStrategy
  else .hftOtherStrategy

def ofByte (byte : UInt8) : OrderClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderClassification) : ofByte value.toByte = value := by
  cases value with
  | nonHft => decide
  | hftMarketMakingStrategy => decide
  | hftArbitrageStrategy => decide
  | hftDirectionalStrategy => decide
  | hftOtherStrategy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderClassification) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderClassification

/-- Cash Margin Type: one byte code -/
def CashMarginType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive CashMarginType where
  | cash -- Cash
  | marginOpenNegotiable -- Margin Open Negotiable
  | marginCloseNegotiable -- Margin Close Negotiable
  | marginOpenStandardized -- Margin Open Standardized
  | marginCloseStandardized -- Margin Close Standardized
  | unlisted (byte : { byte : UInt8 // byte ∉ CashMarginType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CashMarginType

def toByte : CashMarginType → UInt8
  | .cash => 0x31
  | .marginOpenNegotiable => 0x32
  | .marginCloseNegotiable => 0x33
  | .marginOpenStandardized => 0x34
  | .marginCloseStandardized => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CashMarginType :=
  if byte = 0x31 then .cash
  else if byte = 0x32 then .marginOpenNegotiable
  else if byte = 0x33 then .marginCloseNegotiable
  else if byte = 0x34 then .marginOpenStandardized
  else .marginCloseStandardized

def ofByte (byte : UInt8) : CashMarginType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CashMarginType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | marginOpenNegotiable => decide
  | marginCloseNegotiable => decide
  | marginOpenStandardized => decide
  | marginCloseStandardized => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CashMarginType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CashMarginType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CashMarginType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CashMarginType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CashMarginType

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65486
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65486 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65486 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestPacket

/-- Enter Order Message: 47 bytes -/
structure EnterOrderMessage where
  orderToken : BitVec 32
  clientReference : Alpha 10
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderbookId : Alpha 4
  group : Alpha 4
  price : BitVec 32
  timeInForce : BitVec 32
  firmId : BitVec 32
  display : Display
  capacity : Capacity
  minimumQuantity : BitVec 32
  orderClassification : OrderClassification
  cashMarginType : CashMarginType
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  encodeUInt 4 message.orderToken
    ++ (Alpha.encode message.clientReference
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.orderbookId
    ++ (Alpha.encode message.group
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (encodeUInt 4 message.firmId
    ++ (Display.encode message.display
    ++ (Capacity.encode message.capacity
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (OrderClassification.encode message.orderClassification
    ++ (CashMarginType.encode message.cashMarginType)))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (clientReference, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderbookId, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (firmId, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (orderClassification, bytes) ← OrderClassification.decode bytes
  let (cashMarginType, bytes) ← CashMarginType.decode bytes
  pure ({ orderToken, clientReference, buySellIndicator, quantity, orderbookId, group, price, timeInForce, firmId, display, capacity, minimumQuantity, orderClassification, cashMarginType }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BuySellIndicator.encode_length, Display.encode_length, Capacity.encode_length, OrderClassification.encode_length, CashMarginType.encode_length]

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderClassification.decode_encode, some_bind]
  dsimp only
  rw [CashMarginType.decode_encode, some_bind]
  rfl

end EnterOrderMessage

/-- Replace Order Message: 25 bytes -/
structure ReplaceOrderMessage where
  existingOrderToken : BitVec 32
  replacementOrderToken : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  timeInForce : BitVec 32
  display : Display
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUInt 4 message.existingOrderToken
    ++ (encodeUInt 4 message.replacementOrderToken
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Display.encode message.display
    ++ (encodeUInt 4 message.minimumQuantity))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (existingOrderToken, bytes) ← decodeUInt 4 bytes
  let (replacementOrderToken, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ existingOrderToken, replacementOrderToken, quantity, price, timeInForce, display, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Display.encode_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 8 bytes -/
structure CancelOrderMessage where
  orderToken : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUInt 4 message.orderToken
    ++ (encodeUInt 4 message.quantity)

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ orderToken, quantity }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelOrderMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- "U" 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message

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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
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

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 65486 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
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

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 82 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 79 then (LogoutRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutRequest message) else none
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode_nil]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientSoupBinTcpPacket := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientPayload ← ClientPayload.decode clientPacketType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
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
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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

end Omi.OdxOdxequitiesPtsOuchV20Client
