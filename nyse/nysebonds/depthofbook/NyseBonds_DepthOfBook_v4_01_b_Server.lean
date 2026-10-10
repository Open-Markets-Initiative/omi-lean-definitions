import Wire

/-!
# New York Stock Exchange DepthOfBook v4.01.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNysebondsDepthofbookAbpV401BServer

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

/-- System Code: one byte code -/
def SystemCode.codes : List UInt8 :=
  [0x46]

inductive SystemCode where
  | bonds -- Bonds
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemCode

def toByte : SystemCode → UInt8
  | .bonds => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SystemCode :=
  .bonds

def ofByte (byte : UInt8) : SystemCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemCode) : ofByte value.toByte = value := by
  cases value with
  | bonds => decide
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

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
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

/-- Flat Pricing: one byte code -/
def FlatPricing.codes : List UInt8 :=
  [0x46]

inductive FlatPricing where
  | flatPricingIsInEffect -- Flat Pricing Is In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ FlatPricing.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FlatPricing

def toByte : FlatPricing → UInt8
  | .flatPricingIsInEffect => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : FlatPricing :=
  .flatPricingIsInEffect

def ofByte (byte : UInt8) : FlatPricing :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FlatPricing) : ofByte value.toByte = value := by
  cases value with
  | flatPricingIsInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FlatPricing) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FlatPricing × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FlatPricing) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FlatPricing) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FlatPricing

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x4D, 0x48, 0x43]

inductive AuctionType where
  | open_ -- Open
  | market -- Market
  | halt -- Halt
  | closing -- Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .open_ => 0x4F
  | .market => 0x4D
  | .halt => 0x48
  | .closing => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .open_
  else if byte = 0x4D then .market
  else if byte = 0x48 then .halt
  else .closing

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | market => decide
  | halt => decide
  | closing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x43, 0x53, 0x48, 0x55]

inductive EventCode where
  | clearBook -- Clear Book
  | clearBookBySymbol -- Clear Book By Symbol
  | haltSymbol -- Halt Symbol
  | unHaltSymbol -- Un Halt Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .clearBook => 0x43
  | .clearBookBySymbol => 0x53
  | .haltSymbol => 0x48
  | .unHaltSymbol => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x43 then .clearBook
  else if byte = 0x53 then .clearBookBySymbol
  else if byte = 0x48 then .haltSymbol
  else .unHaltSymbol

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | clearBook => decide
  | clearBookBySymbol => decide
  | haltSymbol => decide
  | unHaltSymbol => decide
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

/-- Add Order Message: 76 bytes -/
structure AddOrderMessage where
  time : BitVec 32
  sequenceNumber : BitVec 32
  orderReferenceNumber : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  priceScaleCode : PriceScaleCode
  exchangeCode : ExchangeCode
  systemCode : SystemCode
  buySellIndicator : BuySellIndicator
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  securityType : BitVec 8
  orderType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  quoteId : Alpha 5
  paddingAscii3 : Alpha 3
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.time
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.orderReferenceNumber
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.price
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (SystemCode.encode message.systemCode
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (encodeUIntLE 1 message.securityType
    ++ (encodeUIntLE 1 message.orderType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.quoteId
    ++ (Alpha.encode message.paddingAscii3
    ++ (encodeUIntLE 4 message.minimumQuantity)))))))))))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (quoteId, bytes) ← Alpha.decode 5 bytes
  let (paddingAscii3, bytes) ← Alpha.decode 3 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ time, sequenceNumber, orderReferenceNumber, quantity, price, priceScaleCode, exchangeCode, systemCode, buySellIndicator, flatPricing, tradingAction, securityType, orderType, nyseBondSymbol, cusipIsin, quoteId, paddingAscii3, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, ExchangeCode.encode_length, SystemCode.encode_length, BuySellIndicator.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMessage

/-- Modify Order Message: 76 bytes -/
structure ModifyOrderMessage where
  time : BitVec 32
  sequenceNumber : BitVec 32
  orderReferenceNumber : BitVec 32
  quantity : BitVec 32
  price : BitVec 32
  priceScaleCode : PriceScaleCode
  exchangeCode : ExchangeCode
  systemCode : SystemCode
  buySellIndicator : BuySellIndicator
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  securityType : BitVec 8
  orderType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  quoteId : Alpha 5
  paddingAscii3 : Alpha 3
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.time
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.orderReferenceNumber
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.price
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (SystemCode.encode message.systemCode
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (encodeUIntLE 1 message.securityType
    ++ (encodeUIntLE 1 message.orderType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.quoteId
    ++ (Alpha.encode message.paddingAscii3
    ++ (encodeUIntLE 4 message.minimumQuantity)))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (quoteId, bytes) ← Alpha.decode 5 bytes
  let (paddingAscii3, bytes) ← Alpha.decode 3 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ time, sequenceNumber, orderReferenceNumber, quantity, price, priceScaleCode, exchangeCode, systemCode, buySellIndicator, flatPricing, tradingAction, securityType, orderType, nyseBondSymbol, cusipIsin, quoteId, paddingAscii3, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, ExchangeCode.encode_length, SystemCode.encode_length, BuySellIndicator.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrderMessage

/-- Delete Order Message: 60 bytes -/
structure DeleteOrderMessage where
  time : BitVec 32
  sequenceNumber : BitVec 32
  orderReferenceNumber : BitVec 32
  exchangeCode : ExchangeCode
  systemCode : SystemCode
  buySellIndicator : BuySellIndicator
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  securityType : BitVec 8
  orderType : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  quoteId : Alpha 5
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.time
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.orderReferenceNumber
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (SystemCode.encode message.systemCode
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (encodeUIntLE 1 message.securityType
    ++ (encodeUIntLE 1 message.orderType
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.quoteId))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (quoteId, bytes) ← Alpha.decode 5 bytes
  pure ({ time, sequenceNumber, orderReferenceNumber, exchangeCode, systemCode, buySellIndicator, flatPricing, tradingAction, securityType, orderType, nyseBondSymbol, cusipIsin, quoteId }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExchangeCode.encode_length, SystemCode.encode_length, BuySellIndicator.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : DeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end DeleteOrderMessage

/-- Imbalance Message: 72 bytes -/
structure ImbalanceMessage where
  time : BitVec 32
  sequenceNumber : BitVec 32
  matchQuantity : BitVec 32
  totalImbalance : BitVec 32
  marketImbalance : BitVec 32
  price : BitVec 32
  priceScaleCode : PriceScaleCode
  exchangeCode : ExchangeCode
  systemCode : SystemCode
  auctionType : AuctionType
  flatPricing : FlatPricing
  tradingAction : BitVec 8
  securityType : BitVec 8
  quoteCondition : BitVec 8
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  auctionTime : Alpha 4
  deriving DecidableEq, Repr

namespace ImbalanceMessage

def encode (message : ImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.time
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.matchQuantity
    ++ (encodeUIntLE 4 message.totalImbalance
    ++ (encodeUIntLE 4 message.marketImbalance
    ++ (encodeUIntLE 4 message.price
    ++ (PriceScaleCode.encode message.priceScaleCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (SystemCode.encode message.systemCode
    ++ (AuctionType.encode message.auctionType
    ++ (FlatPricing.encode message.flatPricing
    ++ (encodeUIntLE 1 message.tradingAction
    ++ (encodeUIntLE 1 message.securityType
    ++ (encodeUIntLE 1 message.quoteCondition
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.auctionTime))))))))))))))))

def decode (bytes : List UInt8) : Option (ImbalanceMessage × List UInt8) := do
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (matchQuantity, bytes) ← decodeUIntLE 4 bytes
  let (totalImbalance, bytes) ← decodeUIntLE 4 bytes
  let (marketImbalance, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← PriceScaleCode.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (flatPricing, bytes) ← FlatPricing.decode bytes
  let (tradingAction, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (quoteCondition, bytes) ← decodeUIntLE 1 bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (auctionTime, bytes) ← Alpha.decode 4 bytes
  pure ({ time, sequenceNumber, matchQuantity, totalImbalance, marketImbalance, price, priceScaleCode, exchangeCode, systemCode, auctionType, flatPricing, tradingAction, securityType, quoteCondition, nyseBondSymbol, cusipIsin, auctionTime }, bytes)

@[simp] theorem encode_length (message : ImbalanceMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PriceScaleCode.encode_length, ExchangeCode.encode_length, SystemCode.encode_length, AuctionType.encode_length, FlatPricing.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PriceScaleCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlatPricing.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end ImbalanceMessage

/-- System Event Message: 52 bytes -/
structure SystemEventMessage where
  time : BitVec 32
  sequenceNumber : BitVec 32
  nextExpectedSequenceNumber : BitVec 32
  eventCode : EventCode
  systemCode : SystemCode
  nyseBondSymbol : Alpha 22
  cusipIsin : Alpha 14
  paddingAscii2 : Alpha 2
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 4 message.time
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.nextExpectedSequenceNumber
    ++ (EventCode.encode message.eventCode
    ++ (SystemCode.encode message.systemCode
    ++ (Alpha.encode message.nyseBondSymbol
    ++ (Alpha.encode message.cusipIsin
    ++ (Alpha.encode message.paddingAscii2)))))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (nextExpectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (systemCode, bytes) ← SystemCode.decode bytes
  let (nyseBondSymbol, bytes) ← Alpha.decode 22 bytes
  let (cusipIsin, bytes) ← Alpha.decode 14 bytes
  let (paddingAscii2, bytes) ← Alpha.decode 2 bytes
  pure ({ time, sequenceNumber, nextExpectedSequenceNumber, eventCode, systemCode, nyseBondSymbol, cusipIsin, paddingAscii2 }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventCode.encode_length, SystemCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SystemCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginAcceptedMessage (message : LoginAcceptedMessage) -- "Q" 0x51
  | loginRejectedMessage (message : LoginRejectedMessage) -- "R" 0x52
  | heartbeatMessage (message : HeartbeatMessage) -- "H" 0x48
  | testResponseMessage (message : TestResponseMessage) -- "S" 0x53
  | addOrderMessage (message : AddOrderMessage) -- "N" 0x4E
  | modifyOrderMessage (message : ModifyOrderMessage) -- "C" 0x43
  | deleteOrderMessage (message : DeleteOrderMessage) -- "K" 0x4B
  | imbalanceMessage (message : ImbalanceMessage) -- "W" 0x57
  | systemEventMessage (message : SystemEventMessage) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginAcceptedMessage _ => 81
  | .loginRejectedMessage _ => 82
  | .heartbeatMessage _ => 72
  | .testResponseMessage _ => 83
  | .addOrderMessage _ => 78
  | .modifyOrderMessage _ => 67
  | .deleteOrderMessage _ => 75
  | .imbalanceMessage _ => 87
  | .systemEventMessage _ => 89

def encode : Payload → List UInt8
  | .loginAcceptedMessage message => LoginAcceptedMessage.encode message
  | .loginRejectedMessage message => LoginRejectedMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testResponseMessage message => TestResponseMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .imbalanceMessage message => ImbalanceMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 76 := by
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
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [encode, DeleteOrderMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [encode, ImbalanceMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 81 then (LoginAcceptedMessage.decode bytes).map fun (message, rest) => (.loginAcceptedMessage message, rest)
  else if tag = 82 then (LoginRejectedMessage.decode bytes).map fun (message, rest) => (.loginRejectedMessage message, rest)
  else if tag = 72 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 83 then (TestResponseMessage.decode bytes).map fun (message, rest) => (.testResponseMessage message, rest)
  else if tag = 78 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 67 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 75 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 87 then (ImbalanceMessage.decode bytes).map fun (message, rest) => (.imbalanceMessage message, rest)
  else if tag = 89 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 80 := by
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
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DeleteOrderMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ImbalanceMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SystemEventMessage.encode_length]
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

end Omi.NyseNysebondsDepthofbookAbpV401BServer
