import Omi.Wire

/-!
# Box Options Market Sola Trade Reporting v4.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BoxBoxoptionsSolatradereportingAtrV45Client

/-- Message Flag: one byte code -/
def MessageFlag.codes : List UInt8 :=
  [0x52, 0x44]

inductive MessageFlag where
  | retransmittedMessage -- Retransmitted Message
  | duplicatedMessage -- Duplicated Message
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageFlag

def toByte : MessageFlag → UInt8
  | .retransmittedMessage => 0x52
  | .duplicatedMessage => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageFlag :=
  if byte = 0x52 then .retransmittedMessage
  else .duplicatedMessage

def ofByte (byte : UInt8) : MessageFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageFlag) : ofByte value.toByte = value := by
  cases value with
  | retransmittedMessage => decide
  | duplicatedMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MessageFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageFlag

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive AccountType where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | floorBrokerCustomer -- Floor Broker Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | floorBrokerDealer -- Floor Broker Dealer
  | floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing -- Floor Market Maker Flex Symbology Symbol Is Prefixed By One Of The Following
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .floorBrokerCustomer => 0x56
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .floorBrokerDealer => 0x59
  | .floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x56 then .floorBrokerCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else if byte = 0x58 then .awayMarketMaker
  else if byte = 0x59 then .floorBrokerDealer
  else .floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | floorBrokerCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | floorBrokerDealer => decide
  | floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Start Of Day Acknowledgement: 0 bytes -/
structure StartOfDayAcknowledgement where
  deriving DecidableEq, Repr

namespace StartOfDayAcknowledgement

def encode (_ : StartOfDayAcknowledgement) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfDayAcknowledgement × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfDayAcknowledgement) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfDayAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfDayAcknowledgement

/-- Circuit Response: 0 bytes -/
structure CircuitResponse where
  deriving DecidableEq, Repr

namespace CircuitResponse

def encode (_ : CircuitResponse) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (CircuitResponse × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : CircuitResponse) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : CircuitResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end CircuitResponse

/-- Restart Request: 8 bytes -/
structure RestartRequest where
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace RestartRequest

def encode (message : RestartRequest) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (RestartRequest × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : RestartRequest) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RestartRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RestartRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RestartRequest

/-- Client Signon: 36 bytes -/
structure ClientSignon where
  memberNumber : Alpha 4
  initialSequenceNumber : Alpha 8
  protocolVersion : Alpha 2
  time : Alpha 6
  username : Alpha 8
  passwordMd5Encryption : Alpha 8
  deriving DecidableEq, Repr

namespace ClientSignon

def encode (message : ClientSignon) : List UInt8 :=
  Alpha.encode message.memberNumber
    ++ (Alpha.encode message.initialSequenceNumber
    ++ (Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.time
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.passwordMd5Encryption)))))

def decode (bytes : List UInt8) : Option (ClientSignon × List UInt8) := do
  let (memberNumber, bytes) ← Alpha.decode 4 bytes
  let (initialSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (protocolVersion, bytes) ← Alpha.decode 2 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  let (username, bytes) ← Alpha.decode 8 bytes
  let (passwordMd5Encryption, bytes) ← Alpha.decode 8 bytes
  pure ({ memberNumber, initialSequenceNumber, protocolVersion, time, username, passwordMd5Encryption }, bytes)

@[simp] theorem encode_length (message : ClientSignon) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClientSignon) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientSignon) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClientSignon

/-- New Allocation: 94 bytes -/
structure NewAllocation where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  giveUpFirm : Alpha 4
  volume : Alpha 8
  accountType : AccountType
  openClose : OpenClose
  clientAccountNumber : Alpha 12
  subtraderId : Alpha 3
  cmtaBroker : Alpha 4
  clientMemo : Alpha 16
  additionalFirm : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace NewAllocation

def encode (message : NewAllocation) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber
    ++ (Alpha.encode message.giveUpFirm
    ++ (Alpha.encode message.volume
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.subtraderId
    ++ (Alpha.encode message.cmtaBroker
    ++ (Alpha.encode message.clientMemo
    ++ (Alpha.encode message.additionalFirm
    ++ (Alpha.encode message.additionalClientMemo)))))))))))

def decode (bytes : List UInt8) : Option (NewAllocation × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  let (giveUpFirm, bytes) ← Alpha.decode 4 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (additionalFirm, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ referenceTransactionId, referenceTradeNumber, giveUpFirm, volume, accountType, openClose, clientAccountNumber, subtraderId, cmtaBroker, clientMemo, additionalFirm, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : NewAllocation) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : NewAllocation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewAllocation) (rest : List UInt8) :
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewAllocation

/-- Modify Allocation: 94 bytes -/
structure ModifyAllocation where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  giveUpFirm : Alpha 4
  volume : Alpha 8
  accountType : AccountType
  openClose : OpenClose
  clientAccountNumber : Alpha 12
  subtraderId : Alpha 3
  cmtaBroker : Alpha 4
  clientMemo : Alpha 16
  additionalFirm : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace ModifyAllocation

def encode (message : ModifyAllocation) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber
    ++ (Alpha.encode message.giveUpFirm
    ++ (Alpha.encode message.volume
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.subtraderId
    ++ (Alpha.encode message.cmtaBroker
    ++ (Alpha.encode message.clientMemo
    ++ (Alpha.encode message.additionalFirm
    ++ (Alpha.encode message.additionalClientMemo)))))))))))

def decode (bytes : List UInt8) : Option (ModifyAllocation × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  let (giveUpFirm, bytes) ← Alpha.decode 4 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (additionalFirm, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ referenceTransactionId, referenceTradeNumber, giveUpFirm, volume, accountType, openClose, clientAccountNumber, subtraderId, cmtaBroker, clientMemo, additionalFirm, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : ModifyAllocation) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : ModifyAllocation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyAllocation) (rest : List UInt8) :
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyAllocation

/-- Delete Allocation: 25 bytes -/
structure DeleteAllocation where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  deriving DecidableEq, Repr

namespace DeleteAllocation

def encode (message : DeleteAllocation) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber)

def decode (bytes : List UInt8) : Option (DeleteAllocation × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  pure ({ referenceTransactionId, referenceTradeNumber }, bytes)

@[simp] theorem encode_length (message : DeleteAllocation) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DeleteAllocation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllocation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteAllocation

/-- New Give Up: 94 bytes -/
structure NewGiveUp where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  giveUpFirm : Alpha 4
  volume : Alpha 8
  accountType : AccountType
  openClose : OpenClose
  clientAccountNumber : Alpha 12
  subtraderId : Alpha 3
  cmtaBroker : Alpha 4
  clientMemo : Alpha 16
  additionalFirm : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace NewGiveUp

def encode (message : NewGiveUp) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber
    ++ (Alpha.encode message.giveUpFirm
    ++ (Alpha.encode message.volume
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.subtraderId
    ++ (Alpha.encode message.cmtaBroker
    ++ (Alpha.encode message.clientMemo
    ++ (Alpha.encode message.additionalFirm
    ++ (Alpha.encode message.additionalClientMemo)))))))))))

def decode (bytes : List UInt8) : Option (NewGiveUp × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  let (giveUpFirm, bytes) ← Alpha.decode 4 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (additionalFirm, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ referenceTransactionId, referenceTradeNumber, giveUpFirm, volume, accountType, openClose, clientAccountNumber, subtraderId, cmtaBroker, clientMemo, additionalFirm, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : NewGiveUp) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : NewGiveUp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewGiveUp) (rest : List UInt8) :
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewGiveUp

/-- Modify Give Up: 94 bytes -/
structure ModifyGiveUp where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  giveUpFirm : Alpha 4
  volume : Alpha 8
  accountType : AccountType
  openClose : OpenClose
  clientAccountNumber : Alpha 12
  subtraderId : Alpha 3
  cmtaBroker : Alpha 4
  clientMemo : Alpha 16
  additionalFirm : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace ModifyGiveUp

def encode (message : ModifyGiveUp) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber
    ++ (Alpha.encode message.giveUpFirm
    ++ (Alpha.encode message.volume
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.subtraderId
    ++ (Alpha.encode message.cmtaBroker
    ++ (Alpha.encode message.clientMemo
    ++ (Alpha.encode message.additionalFirm
    ++ (Alpha.encode message.additionalClientMemo)))))))))))

def decode (bytes : List UInt8) : Option (ModifyGiveUp × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  let (giveUpFirm, bytes) ← Alpha.decode 4 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (additionalFirm, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ referenceTransactionId, referenceTradeNumber, giveUpFirm, volume, accountType, openClose, clientAccountNumber, subtraderId, cmtaBroker, clientMemo, additionalFirm, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : ModifyGiveUp) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : ModifyGiveUp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyGiveUp) (rest : List UInt8) :
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyGiveUp

/-- Delete Give Up: 25 bytes -/
structure DeleteGiveUp where
  referenceTransactionId : Alpha 10
  referenceTradeNumber : Alpha 15
  deriving DecidableEq, Repr

namespace DeleteGiveUp

def encode (message : DeleteGiveUp) : List UInt8 :=
  Alpha.encode message.referenceTransactionId
    ++ (Alpha.encode message.referenceTradeNumber)

def decode (bytes : List UInt8) : Option (DeleteGiveUp × List UInt8) := do
  let (referenceTransactionId, bytes) ← Alpha.decode 10 bytes
  let (referenceTradeNumber, bytes) ← Alpha.decode 15 bytes
  pure ({ referenceTransactionId, referenceTradeNumber }, bytes)

@[simp] theorem encode_length (message : DeleteGiveUp) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DeleteGiveUp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteGiveUp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteGiveUp

/-- Any Client Message, selected by Message Type -/
inductive ClientMessage where
  | startOfDayAcknowledgement (message : StartOfDayAcknowledgement) -- "01" 0x3031
  | circuitResponse (message : CircuitResponse) -- "03" 0x3033
  | restartRequest (message : RestartRequest) -- "04" 0x3034
  | clientSignon (message : ClientSignon) -- "09" 0x3039
  | newAllocation (message : NewAllocation) -- "42" 0x3432
  | modifyAllocation (message : ModifyAllocation) -- "43" 0x3433
  | deleteAllocation (message : DeleteAllocation) -- "44" 0x3434
  | newGiveUp (message : NewGiveUp) -- "52" 0x3532
  | modifyGiveUp (message : ModifyGiveUp) -- "53" 0x3533
  | deleteGiveUp (message : DeleteGiveUp) -- "54" 0x3534
  deriving DecidableEq, Repr

namespace ClientMessage

/-- The Message Type each message is sent under -/
def tag : ClientMessage → BitVec 16
  | .startOfDayAcknowledgement _ => 12337
  | .circuitResponse _ => 12339
  | .restartRequest _ => 12340
  | .clientSignon _ => 12345
  | .newAllocation _ => 13362
  | .modifyAllocation _ => 13363
  | .deleteAllocation _ => 13364
  | .newGiveUp _ => 13618
  | .modifyGiveUp _ => 13619
  | .deleteGiveUp _ => 13620

def encode : ClientMessage → List UInt8
  | .startOfDayAcknowledgement message => StartOfDayAcknowledgement.encode message
  | .circuitResponse message => CircuitResponse.encode message
  | .restartRequest message => RestartRequest.encode message
  | .clientSignon message => ClientSignon.encode message
  | .newAllocation message => NewAllocation.encode message
  | .modifyAllocation message => ModifyAllocation.encode message
  | .deleteAllocation message => DeleteAllocation.encode message
  | .newGiveUp message => NewGiveUp.encode message
  | .modifyGiveUp message => ModifyGiveUp.encode message
  | .deleteGiveUp message => DeleteGiveUp.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessage) : (encode message).length ≤ 94 := by
  cases message with
  | startOfDayAcknowledgement inner =>
    simp only [encode, StartOfDayAcknowledgement.encode_length]
    omega
  | circuitResponse inner =>
    simp only [encode, CircuitResponse.encode_length]
    omega
  | restartRequest inner =>
    simp only [encode, RestartRequest.encode_length]
    omega
  | clientSignon inner =>
    simp only [encode, ClientSignon.encode_length]
    omega
  | newAllocation inner =>
    simp only [encode, NewAllocation.encode_length]
    omega
  | modifyAllocation inner =>
    simp only [encode, ModifyAllocation.encode_length]
    omega
  | deleteAllocation inner =>
    simp only [encode, DeleteAllocation.encode_length]
    omega
  | newGiveUp inner =>
    simp only [encode, NewGiveUp.encode_length]
    omega
  | modifyGiveUp inner =>
    simp only [encode, ModifyGiveUp.encode_length]
    omega
  | deleteGiveUp inner =>
    simp only [encode, DeleteGiveUp.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessage × List UInt8) :=
  if tag = 12337 then (StartOfDayAcknowledgement.decode bytes).map fun (message, rest) => (.startOfDayAcknowledgement message, rest)
  else if tag = 12339 then (CircuitResponse.decode bytes).map fun (message, rest) => (.circuitResponse message, rest)
  else if tag = 12340 then (RestartRequest.decode bytes).map fun (message, rest) => (.restartRequest message, rest)
  else if tag = 12345 then (ClientSignon.decode bytes).map fun (message, rest) => (.clientSignon message, rest)
  else if tag = 13362 then (NewAllocation.decode bytes).map fun (message, rest) => (.newAllocation message, rest)
  else if tag = 13363 then (ModifyAllocation.decode bytes).map fun (message, rest) => (.modifyAllocation message, rest)
  else if tag = 13364 then (DeleteAllocation.decode bytes).map fun (message, rest) => (.deleteAllocation message, rest)
  else if tag = 13618 then (NewGiveUp.decode bytes).map fun (message, rest) => (.newGiveUp message, rest)
  else if tag = 13619 then (ModifyGiveUp.decode bytes).map fun (message, rest) => (.modifyGiveUp message, rest)
  else if tag = 13620 then (DeleteGiveUp.decode bytes).map fun (message, rest) => (.deleteGiveUp message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  source : Alpha 4
  destination : Alpha 4
  messageFlag : MessageFlag
  controlByte : Alpha 1
  sequenceNumber : Alpha 8
  acknowledgementSequenceNumber : Alpha 8
  clientMessage : ClientMessage
  endOfText : BitVec 8
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.destination
    ++ (encodeUInt 2 (ClientMessage.tag message.clientMessage)
    ++ (MessageFlag.encode message.messageFlag
    ++ (Alpha.encode message.controlByte
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.acknowledgementSequenceNumber
    ++ (ClientMessage.encode message.clientMessage
    ++ (encodeUInt 1 message.endOfText))))))))

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (source, bytes) ← Alpha.decode 4 bytes
  let (destination, bytes) ← Alpha.decode 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageFlag, bytes) ← MessageFlag.decode bytes
  let (controlByte, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (acknowledgementSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (clientMessage, bytes) ← ClientMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  pure ({ source, destination, messageFlag, controlByte, sequenceNumber, acknowledgementSequenceNumber, clientMessage, endOfText }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientPacket) : (encode message).length ≤ 123 := by
  unfold encode
  cases message.clientMessage with
  | startOfDayAcknowledgement inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, StartOfDayAcknowledgement.encode_length]
    omega
  | circuitResponse inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, CircuitResponse.encode_length]
    omega
  | restartRequest inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, RestartRequest.encode_length]
    omega
  | clientSignon inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, ClientSignon.encode_length]
    omega
  | newAllocation inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, NewAllocation.encode_length]
    omega
  | modifyAllocation inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, ModifyAllocation.encode_length]
    omega
  | deleteAllocation inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, DeleteAllocation.encode_length]
    omega
  | newGiveUp inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, NewGiveUp.encode_length]
    omega
  | modifyGiveUp inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, ModifyGiveUp.encode_length]
    omega
  | deleteGiveUp inner =>
    simp only [ClientMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, DeleteGiveUp.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClientMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClientPacket

end Omi.BoxBoxoptionsSolatradereportingAtrV45Client
