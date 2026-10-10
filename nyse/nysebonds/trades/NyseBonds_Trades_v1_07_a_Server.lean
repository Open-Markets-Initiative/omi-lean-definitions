import Wire

/-!
# New York Stock Exchange Trades v1.07.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNysebondsTradesAbpV107AServer

/-- Reject Code: one byte code -/
def RejectCode.codes : List UInt8 :=
  [0x41, 0x4D, 0x52, 0x53, 0x54]

inductive RejectCode where
  | notAuthorized -- Not Authorized
  | maximumServerConnectionsReached -- Maximum Server Connections Reached
  | invalidSubscription -- Invalid Subscription
  | invalidSequence -- Invalid Sequence
  | timeout -- Timeout
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectCode

def toByte : RejectCode → UInt8
  | .notAuthorized => 0x41
  | .maximumServerConnectionsReached => 0x4D
  | .invalidSubscription => 0x52
  | .invalidSequence => 0x53
  | .timeout => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectCode :=
  if byte = 0x41 then .notAuthorized
  else if byte = 0x4D then .maximumServerConnectionsReached
  else if byte = 0x52 then .invalidSubscription
  else if byte = 0x53 then .invalidSequence
  else .timeout

def ofByte (byte : UInt8) : RejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | maximumServerConnectionsReached => decide
  | invalidSubscription => decide
  | invalidSequence => decide
  | timeout => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectCode

/-- Price Scale Code: one byte code -/
def PriceScaleCode.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive PriceScaleCode where
  | noDivision -- No Division
  | ten -- Ten
  | oneHundred -- One Hundred
  | oneThousand -- One Thousand
  | tenThousand -- Ten Thousand
  | oneHundredThousand -- One Hundred Thousand
  | oneMillion -- One Million
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceScaleCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceScaleCode

def toByte : PriceScaleCode → UInt8
  | .noDivision => 0x30
  | .ten => 0x31
  | .oneHundred => 0x32
  | .oneThousand => 0x33
  | .tenThousand => 0x34
  | .oneHundredThousand => 0x35
  | .oneMillion => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceScaleCode :=
  if byte = 0x30 then .noDivision
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .oneHundred
  else if byte = 0x33 then .oneThousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .oneHundredThousand
  else .oneMillion

def ofByte (byte : UInt8) : PriceScaleCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceScaleCode) : ofByte value.toByte = value := by
  cases value with
  | noDivision => decide
  | ten => decide
  | oneHundred => decide
  | oneThousand => decide
  | tenThousand => decide
  | oneHundredThousand => decide
  | oneMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceScaleCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceScaleCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceScaleCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceScaleCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceScaleCode

/-- System Code: one byte code -/
def SystemCode.codes : List UInt8 :=
  [0x46]

inductive SystemCode where
  | bondsTradingPlatform -- Bonds Trading Platform
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemCode

def toByte : SystemCode → UInt8
  | .bondsTradingPlatform => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SystemCode :=
  .bondsTradingPlatform

def ofByte (byte : UInt8) : SystemCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemCode) : ofByte value.toByte = value := by
  cases value with
  | bondsTradingPlatform => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemCode

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x4E]

inductive ExchangeCode where
  | nyseListedBond -- Nyse Listed Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyseListedBond => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ExchangeCode :=
  .nyseListedBond

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyseListedBond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x42, 0x43]

inductive EventCode where
  | tradeBust -- Trade Bust
  | tradeCorrection -- Trade Correction
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .tradeBust => 0x42
  | .tradeCorrection => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x42 then .tradeBust
  else .tradeCorrection

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | tradeBust => decide
  | tradeCorrection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Login Accepted Message: 6 bytes -/
structure LoginAcceptedMessage where
  versionId : Alpha 5
  paddingAscii1 : Alpha 1
  deriving DecidableEq, Repr

namespace LoginAcceptedMessage

def encode (message : LoginAcceptedMessage) : List UInt8 :=
  Alpha.encode message.versionId
    ++ (Alpha.encode message.paddingAscii1)

def decode (bytes : List UInt8) : Option (LoginAcceptedMessage × List UInt8) := do
  let (versionId, bytes) ← Alpha.decode 5 bytes
  let (paddingAscii1, bytes) ← Alpha.decode 1 bytes
  pure ({ versionId, paddingAscii1 }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedMessage

/-- Login Rejected Message: 2 bytes -/
structure LoginRejectedMessage where
  rejectCode : RejectCode
  paddingAscii1 : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedMessage

def encode (message : LoginRejectedMessage) : List UInt8 :=
  RejectCode.encode message.rejectCode
    ++ (Alpha.encode message.paddingAscii1)

def decode (bytes : List UInt8) : Option (LoginRejectedMessage × List UInt8) := do
  let (rejectCode, bytes) ← RejectCode.decode bytes
  let (paddingAscii1, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectCode, paddingAscii1 }, bytes)

@[simp] theorem encode_length (message : LoginRejectedMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, RejectCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, RejectCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Test Response Message: 20 bytes -/
structure TestResponseMessage where
  testMessage : Alpha 20
  deriving DecidableEq, Repr

namespace TestResponseMessage

def encode (message : TestResponseMessage) : List UInt8 :=
  Alpha.encode message.testMessage

def decode (bytes : List UInt8) : Option (TestResponseMessage × List UInt8) := do
  let (testMessage, bytes) ← Alpha.decode 20 bytes
  pure ({ testMessage }, bytes)

@[simp] theorem encode_length (message : TestResponseMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TestResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TestResponseMessage

/-- Last Sale Message: 64 bytes -/
structure LastSaleMessage where
  lastSaleTime : BitVec 32
  sequenceNumber : BitVec 32
  tradeReferenceNumber : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  priceScaleCode : PriceScaleCode
  systemCode : SystemCode
  exchangeCode : ExchangeCode
  tradeCondition : BitVec 8
  securityType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  paddingAscii3 : Alpha 3
  deriving DecidableEq, Repr

namespace LastSaleMessage

def encode (message : LastSaleMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSaleTime
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.tradeReferenceNumber
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.price
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (SystemCode.encode message.systemCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.tradeCondition
    ++ (encodeUIntLE 1 message.securityType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.paddingAscii3))))))))))))

def decode (bytes : List UInt8) : Option (LastSaleMessage × List UInt8) := do
  let (lastSaleTime, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (tradeCondition, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (paddingAscii3, bytes) ← Alpha.decode 3 bytes
  pure ({ lastSaleTime, sequenceNumber, tradeReferenceNumber, quantity, price, priceScaleCode, systemCode, exchangeCode, tradeCondition, securityType, nyseBondSymbol, cusipIsin, paddingAscii3 }, bytes)

@[simp] theorem encode_length (message : LastSaleMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, SystemCode.encode_length, ExchangeCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : LastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastSaleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceScaleCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LastSaleMessage

/-- Trade Bust Or Correction Message: 64 bytes -/
structure TradeBustOrCorrectionMessage where
  lastSaleTime : BitVec 32
  sequenceNumber : BitVec 32
  tradeReferenceNumber : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  priceScaleCode : PriceScaleCode
  systemCode : SystemCode
  eventCode : EventCode
  exchangeCode : ExchangeCode
  tradeCondition : BitVec 8
  securityType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  paddingAscii2 : Alpha 2
  deriving DecidableEq, Repr

namespace TradeBustOrCorrectionMessage

def encode (message : TradeBustOrCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSaleTime
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.tradeReferenceNumber
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.price
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (SystemCode.encode message.systemCode
    ++ (EventCode.encode message.eventCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.tradeCondition
    ++ (encodeUIntLE 1 message.securityType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.paddingAscii2)))))))))))))

def decode (bytes : List UInt8) : Option (TradeBustOrCorrectionMessage × List UInt8) := do
  let (lastSaleTime, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (tradeCondition, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (paddingAscii2, bytes) ← Alpha.decode 2 bytes
  pure ({ lastSaleTime, sequenceNumber, tradeReferenceNumber, quantity, price, priceScaleCode, systemCode, eventCode, exchangeCode, tradeCondition, securityType, nyseBondSymbol, cusipIsin, paddingAscii2 }, bytes)

@[simp] theorem encode_length (message : TradeBustOrCorrectionMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, SystemCode.encode_length, EventCode.encode_length, ExchangeCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeBustOrCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustOrCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceScaleCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeBustOrCorrectionMessage

/-- Nyse Bond Closing Price Message: 64 bytes -/
structure NyseBondClosingPriceMessage where
  closingTime : BitVec 32
  sequenceNumber : BitVec 32
  tradeReferenceNumber : BitVec 32
  quantity : BitVec 32
  closingPrice : BitVec 32
  priceScaleCode : PriceScaleCode
  systemCode : SystemCode
  exchangeCode : ExchangeCode
  tradeCondition : BitVec 8
  securityType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  paddingAscii3 : Alpha 3
  deriving DecidableEq, Repr

namespace NyseBondClosingPriceMessage

def encode (message : NyseBondClosingPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.closingTime
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.tradeReferenceNumber
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.closingPrice
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (SystemCode.encode message.systemCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.tradeCondition
    ++ (encodeUIntLE 1 message.securityType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.paddingAscii3))))))))))))

def decode (bytes : List UInt8) : Option (NyseBondClosingPriceMessage × List UInt8) := do
  let (closingTime, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (closingPrice, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (tradeCondition, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (paddingAscii3, bytes) ← Alpha.decode 3 bytes
  pure ({ closingTime, sequenceNumber, tradeReferenceNumber, quantity, closingPrice, priceScaleCode, systemCode, exchangeCode, tradeCondition, securityType, nyseBondSymbol, cusipIsin, paddingAscii3 }, bytes)

@[simp] theorem encode_length (message : NyseBondClosingPriceMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, SystemCode.encode_length, ExchangeCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NyseBondClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NyseBondClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceScaleCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NyseBondClosingPriceMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginAcceptedMessage (message : LoginAcceptedMessage) -- "Q" 0x51
  | loginRejectedMessage (message : LoginRejectedMessage) -- "R" 0x52
  | heartbeatMessage (message : HeartbeatMessage) -- "H" 0x48
  | testResponseMessage (message : TestResponseMessage) -- "S" 0x53
  | lastSaleMessage (message : LastSaleMessage) -- "X" 0x58
  | tradeBustOrCorrectionMessage (message : TradeBustOrCorrectionMessage) -- "U" 0x55
  | nyseBondClosingPriceMessage (message : NyseBondClosingPriceMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginAcceptedMessage _ => 81
  | .loginRejectedMessage _ => 82
  | .heartbeatMessage _ => 72
  | .testResponseMessage _ => 83
  | .lastSaleMessage _ => 88
  | .tradeBustOrCorrectionMessage _ => 85
  | .nyseBondClosingPriceMessage _ => 90

def encode : Payload → List UInt8
  | .loginAcceptedMessage message => LoginAcceptedMessage.encode message
  | .loginRejectedMessage message => LoginRejectedMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testResponseMessage message => TestResponseMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
  | .tradeBustOrCorrectionMessage message => TradeBustOrCorrectionMessage.encode message
  | .nyseBondClosingPriceMessage message => NyseBondClosingPriceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 64 := by
  cases message with
  | loginAcceptedMessage inner =>
    simp only [encode, LoginAcceptedMessage.encode_length]
    omega
  | loginRejectedMessage inner =>
    simp only [encode, LoginRejectedMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | testResponseMessage inner =>
    simp only [encode, TestResponseMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [encode, LastSaleMessage.encode_length]
    omega
  | tradeBustOrCorrectionMessage inner =>
    simp only [encode, TradeBustOrCorrectionMessage.encode_length]
    omega
  | nyseBondClosingPriceMessage inner =>
    simp only [encode, NyseBondClosingPriceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 81 then (LoginAcceptedMessage.decode bytes).map fun (message, rest) => (.loginAcceptedMessage message, rest)
  else if tag = 82 then (LoginRejectedMessage.decode bytes).map fun (message, rest) => (.loginRejectedMessage message, rest)
  else if tag = 72 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 83 then (TestResponseMessage.decode bytes).map fun (message, rest) => (.testResponseMessage message, rest)
  else if tag = 88 then (LastSaleMessage.decode bytes).map fun (message, rest) => (.lastSaleMessage message, rest)
  else if tag = 85 then (TradeBustOrCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeBustOrCorrectionMessage message, rest)
  else if tag = 90 then (NyseBondClosingPriceMessage.decode bytes).map fun (message, rest) => (.nyseBondClosingPriceMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  messageBodyLength : BitVec 16
  padding : Alpha 1
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageBodyLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Alpha.encode message.padding
    ++ (Payload.encode message.payload)))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageBodyLength, bytes) ← decodeUInt 2 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (padding, bytes) ← Alpha.decode 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ messageBodyLength, padding, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 68 := by
  unfold encode
  cases message.payload with
  | loginAcceptedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginAcceptedMessage.encode_length]
    omega
  | loginRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginRejectedMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega
  | testResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TestResponseMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LastSaleMessage.encode_length]
    omega
  | tradeBustOrCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeBustOrCorrectionMessage.encode_length]
    omega
  | nyseBondClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NyseBondClosingPriceMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Server Packet -/
structure ServerPacket where
  message : List Message
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option ServerPacket := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end ServerPacket

end Omi.NyseNysebondsTradesAbpV107AServer
