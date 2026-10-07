import Wire

/-!
# The Members Exchange Risk Control v1.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsRiskcontrolSbeV17Client

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Login Request Message: 2 bytes -/
structure LoginRequestMessage where
  tokenType : Alpha 1
  token : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.tokenType
    ++ (Alpha.encode message.token)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (tokenType, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenType, token }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 20 bytes -/
structure ReplayRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  pure ({ sessionId, nextSequenceNumber, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay All Request Message: 8 bytes -/
structure ReplayAllRequestMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayAllRequestMessage

def encode (message : ReplayAllRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (ReplayAllRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : ReplayAllRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayAllRequestMessage

/-- Stream Request Message: 16 bytes -/
structure StreamRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamRequestMessage

def encode (message : StreamRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamRequestMessage

/-- Risk Settings Query Message: 20 bytes -/
structure RiskSettingsQueryMessage where
  clordid : Alpha 20
  deriving DecidableEq, Repr

namespace RiskSettingsQueryMessage

def encode (message : RiskSettingsQueryMessage) : List UInt8 :=
  Alpha.encode message.clordid

def decode (bytes : List UInt8) : Option (RiskSettingsQueryMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  pure ({ clordid }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RiskSettingsQueryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RiskSettingsQueryMessage

/-- Active Risk Threshold Change Request Message: 34 bytes -/
structure ActiveRiskThresholdChangeRequestMessage where
  clOrdIdActiveRiskThresholdChangeRequestClOrdId : Alpha 20
  underlierActiveRiskThresholdChangeRequestUnderlierOptional : Alpha 6
  efidActiveRiskThresholdChangeRequestEfidOptional : Alpha 4
  thresholdQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdChangeRequestMessage

def encode (message : ActiveRiskThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidActiveRiskThresholdChangeRequestEfidOptional
    ++ (encodeUInt 4 message.thresholdQuantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdActiveRiskThresholdChangeRequestClOrdId, underlierActiveRiskThresholdChangeRequestUnderlierOptional, efidActiveRiskThresholdChangeRequestEfidOptional, thresholdQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdChangeRequestMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdChangeRequestMessage

/-- Active Risk Acknowledgement Request Message: 34 bytes -/
structure ActiveRiskAcknowledgementRequestMessage where
  clOrdIdActiveRiskAcknowledgementRequestClOrdId : Alpha 20
  underlierActiveRiskAcknowledgementRequestUnderlier : Alpha 6
  efidActiveRiskAcknowledgementRequestEfid : Alpha 4
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgementRequestMessage

def encode (message : ActiveRiskAcknowledgementRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskAcknowledgementRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskAcknowledgementRequestUnderlier
    ++ (Alpha.encode message.efidActiveRiskAcknowledgementRequestEfid
    ++ (encodeUInt 4 message.quantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgementRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskAcknowledgementRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskAcknowledgementRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskAcknowledgementRequestEfid, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdActiveRiskAcknowledgementRequestClOrdId, underlierActiveRiskAcknowledgementRequestUnderlier, efidActiveRiskAcknowledgementRequestEfid, quantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgementRequestMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgementRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgementRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgementRequestMessage

/-- Cp Volume Threshold Change Request Message: 44 bytes -/
structure CpVolumeThresholdChangeRequestMessage where
  clOrdIdCpVolumeThresholdChangeRequestClOrdId : Alpha 20
  underlierCpVolumeThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpVolumeThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  volume : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpVolumeThresholdChangeRequestMessage

def encode (message : CpVolumeThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpVolumeThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpVolumeThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpVolumeThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpVolumeThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpVolumeThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpVolumeThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpVolumeThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpVolumeThresholdChangeRequestClOrdId, underlierCpVolumeThresholdChangeRequestUnderlierOptional, efidCpVolumeThresholdChangeRequestEfidOptional, riskGroupId, volume, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpVolumeThresholdChangeRequestMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpVolumeThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpVolumeThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpVolumeThresholdChangeRequestMessage

/-- Cp Executed Notional Threshold Change Request Message: 44 bytes -/
structure CpExecutedNotionalThresholdChangeRequestMessage where
  clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpExecutedNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpExecutedNotionalThresholdChangeRequestMessage

def encode (message : CpExecutedNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpExecutedNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpExecutedNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpExecutedNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId, underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional, efidCpExecutedNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpExecutedNotionalThresholdChangeRequestMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpExecutedNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpExecutedNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpExecutedNotionalThresholdChangeRequestMessage

/-- Cp Total Executions Threshold Change Request Message: 40 bytes -/
structure CpTotalExecutionsThresholdChangeRequestMessage where
  clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId : Alpha 20
  underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpTotalExecutionsThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  totalExecutions : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpTotalExecutionsThresholdChangeRequestMessage

def encode (message : CpTotalExecutionsThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpTotalExecutionsThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.totalExecutions
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpTotalExecutionsThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpTotalExecutionsThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (totalExecutions, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId, underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional, efidCpTotalExecutionsThresholdChangeRequestEfidOptional, riskGroupId, totalExecutions, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpTotalExecutionsThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpTotalExecutionsThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpTotalExecutionsThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpTotalExecutionsThresholdChangeRequestMessage

/-- Cp Percent Outstanding Contracts Threshold Change Request Message: 38 bytes -/
structure CpPercentOutstandingContractsThresholdChangeRequestMessage where
  clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId : Alpha 20
  underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional : Alpha 4
  percent : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpPercentOutstandingContractsThresholdChangeRequestMessage

def encode (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional
    ++ (encodeUInt 4 message.percent
    ++ (encodeUInt 4 message.periodInMilliSeconds))))

def decode (bytes : List UInt8) : Option (CpPercentOutstandingContractsThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (percent, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId, underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional, efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional, percent, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpPercentOutstandingContractsThresholdChangeRequestMessage

/-- Cp Breach Count Threshold Change Request Message: 40 bytes -/
structure CpBreachCountThresholdChangeRequestMessage where
  clOrdIdCpBreachCountThresholdChangeRequestClOrdId : Alpha 20
  underlierCpBreachCountThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpBreachCountThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  count : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpBreachCountThresholdChangeRequestMessage

def encode (message : CpBreachCountThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpBreachCountThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpBreachCountThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpBreachCountThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.count
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpBreachCountThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpBreachCountThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpBreachCountThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpBreachCountThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpBreachCountThresholdChangeRequestClOrdId, underlierCpBreachCountThresholdChangeRequestUnderlierOptional, efidCpBreachCountThresholdChangeRequestEfidOptional, riskGroupId, count, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpBreachCountThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpBreachCountThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpBreachCountThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpBreachCountThresholdChangeRequestMessage

/-- Manual Cp Breach Trigger Request Message: 33 bytes -/
structure ManualCpBreachTriggerRequestMessage where
  clOrdIdManualCpBreachTriggerRequestClOrdId : Alpha 20
  underlierManualCpBreachTriggerRequestUnderlierOptional : Alpha 6
  efidManualCpBreachTriggerRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  sendCancels : BitVec 8
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerRequestMessage

def encode (message : ManualCpBreachTriggerRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdManualCpBreachTriggerRequestClOrdId
    ++ (Alpha.encode message.underlierManualCpBreachTriggerRequestUnderlierOptional
    ++ (Alpha.encode message.efidManualCpBreachTriggerRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.sendCancels))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerRequestMessage × List UInt8) := do
  let (clOrdIdManualCpBreachTriggerRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierManualCpBreachTriggerRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidManualCpBreachTriggerRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (sendCancels, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdManualCpBreachTriggerRequestClOrdId, underlierManualCpBreachTriggerRequestUnderlierOptional, efidManualCpBreachTriggerRequestEfidOptional, riskGroupId, sendCancels }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerRequestMessage

/-- Cp Clear Breach Request Message: 28 bytes -/
structure CpClearBreachRequestMessage where
  clOrdIdCpClearBreachRequestClOrdId : Alpha 20
  breachId : BitVec 64
  deriving DecidableEq, Repr

namespace CpClearBreachRequestMessage

def encode (message : CpClearBreachRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearBreachRequestClOrdId
    ++ (encodeUInt 8 message.breachId)

def decode (bytes : List UInt8) : Option (CpClearBreachRequestMessage × List UInt8) := do
  let (clOrdIdCpClearBreachRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (breachId, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpClearBreachRequestClOrdId, breachId }, bytes)

@[simp] theorem encode_length (message : CpClearBreachRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpClearBreachRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearBreachRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpClearBreachRequestMessage

/-- Single Order Allow Iso Orders Change Request Message: 33 bytes -/
structure SingleOrderAllowIsoOrdersChangeRequestMessage where
  clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowIsoOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowIsoOrdersChangeRequestMessage

def encode (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowIsoOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowIsoOrdersChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowIsoOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId, underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional, efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional, riskGroupId, allowIsoOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowIsoOrdersChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowIsoOrdersChangeRequestMessage

/-- Single Order Allow Orders In Crossed Market Change Request Message: 33 bytes -/
structure SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage where
  clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage

def encode (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId, underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional, efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional, riskGroupId, allowOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage

/-- Single Order Max Notional Change Request Message: 40 bytes -/
structure SingleOrderMaxNotionalChangeRequestMessage where
  clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId : Alpha 20
  underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderMaxNotionalChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxNotionalInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace SingleOrderMaxNotionalChangeRequestMessage

def encode (message : SingleOrderMaxNotionalChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderMaxNotionalChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.maxNotionalInDollars))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxNotionalChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderMaxNotionalChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxNotionalInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId, underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional, efidSingleOrderMaxNotionalChangeRequestEfidOptional, riskGroupId, maxNotionalInDollars }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxNotionalChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxNotionalChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxNotionalChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxNotionalChangeRequestMessage

/-- Single Order Max Contracts Change Request Message: 36 bytes -/
structure SingleOrderMaxContractsChangeRequestMessage where
  clOrdIdSingleOrderMaxContractsChangeRequestClOrdId : Alpha 20
  underlierSingleOrderMaxContractsChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderMaxContractsChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleOrderMaxContractsChangeRequestMessage

def encode (message : SingleOrderMaxContractsChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderMaxContractsChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderMaxContractsChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderMaxContractsChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxContracts))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxContractsChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderMaxContractsChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderMaxContractsChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderMaxContractsChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxContracts, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdSingleOrderMaxContractsChangeRequestClOrdId, underlierSingleOrderMaxContractsChangeRequestUnderlierOptional, efidSingleOrderMaxContractsChangeRequestEfidOptional, riskGroupId, maxContracts }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxContractsChangeRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxContractsChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxContractsChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxContractsChangeRequestMessage

/-- Single Order Allow Market Orders Change Request Message: 33 bytes -/
structure SingleOrderAllowMarketOrdersChangeRequestMessage where
  clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowMarketOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowMarketOrdersChangeRequestMessage

def encode (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowMarketOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowMarketOrdersChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowMarketOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId, underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional, efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional, riskGroupId, allowMarketOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowMarketOrdersChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowMarketOrdersChangeRequestMessage

/-- Single Order Restricted Underlier Change Request Message: 33 bytes -/
structure SingleOrderRestrictedUnderlierChangeRequestMessage where
  clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId : Alpha 20
  underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier : Alpha 6
  efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  restricted : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderRestrictedUnderlierChangeRequestMessage

def encode (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier
    ++ (Alpha.encode message.efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.restricted))))

def decode (bytes : List UInt8) : Option (SingleOrderRestrictedUnderlierChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (restricted, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId, underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier, efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional, riskGroupId, restricted }, bytes)

@[simp] theorem encode_length (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderRestrictedUnderlierChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderRestrictedUnderlierChangeRequestMessage

/-- Cp Gross Notional Threshold Change Request Message: 40 bytes -/
structure CpGrossNotionalThresholdChangeRequestMessage where
  clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpGrossNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpGrossNotionalThresholdChangeRequestMessage

def encode (message : CpGrossNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpGrossNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpGrossNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpGrossNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId, underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional, efidCpGrossNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpGrossNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpGrossNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpGrossNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpGrossNotionalThresholdChangeRequestMessage

/-- Cp Market Order Gross Notional Threshold Change Request Message: 40 bytes -/
structure CpMarketOrderGrossNotionalThresholdChangeRequestMessage where
  clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderGrossNotionalThresholdChangeRequestMessage

def encode (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderGrossNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId, underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional, efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderGrossNotionalThresholdChangeRequestMessage

/-- Cp Net Notional Threshold Change Request Message: 40 bytes -/
structure CpNetNotionalThresholdChangeRequestMessage where
  clOrdIdCpNetNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpNetNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpNetNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpNetNotionalThresholdChangeRequestMessage

def encode (message : CpNetNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpNetNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpNetNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpNetNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpNetNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpNetNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpNetNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpNetNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpNetNotionalThresholdChangeRequestClOrdId, underlierCpNetNotionalThresholdChangeRequestUnderlierOptional, efidCpNetNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpNetNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpNetNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpNetNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpNetNotionalThresholdChangeRequestMessage

/-- Cp Market Order Net Notional Threshold Change Request Message: 40 bytes -/
structure CpMarketOrderNetNotionalThresholdChangeRequestMessage where
  clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderNetNotionalThresholdChangeRequestMessage

def encode (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderNetNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId, underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional, efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderNetNotionalThresholdChangeRequestMessage

/-- Cp Duplicate Order Threshold Change Request Message: 41 bytes -/
structure CpDuplicateOrderThresholdChangeRequestMessage where
  clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId : Alpha 20
  underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpDuplicateOrderThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxDupOrders : BitVec 32
  useOrderPriceInDupCheckOptional : BitVec 8
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpDuplicateOrderThresholdChangeRequestMessage

def encode (message : CpDuplicateOrderThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpDuplicateOrderThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxDupOrders
    ++ (encodeUInt 1 message.useOrderPriceInDupCheckOptional
    ++ (encodeUInt 4 message.periodInMilliSeconds))))))

def decode (bytes : List UInt8) : Option (CpDuplicateOrderThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpDuplicateOrderThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxDupOrders, bytes) ← decodeUInt 4 bytes
  let (useOrderPriceInDupCheckOptional, bytes) ← decodeUInt 1 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId, underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional, efidCpDuplicateOrderThresholdChangeRequestEfidOptional, riskGroupId, maxDupOrders, useOrderPriceInDupCheckOptional, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpDuplicateOrderThresholdChangeRequestMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpDuplicateOrderThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpDuplicateOrderThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpDuplicateOrderThresholdChangeRequestMessage

/-- Cp Order Rate Threshold Change Request Message: 40 bytes -/
structure CpOrderRateThresholdChangeRequestMessage where
  clOrdIdCpOrderRateThresholdChangeRequestClOrdId : Alpha 20
  underlierCpOrderRateThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpOrderRateThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxOrderMsgs : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpOrderRateThresholdChangeRequestMessage

def encode (message : CpOrderRateThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpOrderRateThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpOrderRateThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpOrderRateThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxOrderMsgs
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpOrderRateThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpOrderRateThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpOrderRateThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpOrderRateThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxOrderMsgs, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpOrderRateThresholdChangeRequestClOrdId, underlierCpOrderRateThresholdChangeRequestUnderlierOptional, efidCpOrderRateThresholdChangeRequestEfidOptional, riskGroupId, maxOrderMsgs, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpOrderRateThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpOrderRateThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpOrderRateThresholdChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpOrderRateThresholdChangeRequestMessage

/-- Cp Clear All Breaches Request Message: 20 bytes -/
structure CpClearAllBreachesRequestMessage where
  clOrdIdCpClearAllBreachesRequestClOrdId : Alpha 20
  deriving DecidableEq, Repr

namespace CpClearAllBreachesRequestMessage

def encode (message : CpClearAllBreachesRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearAllBreachesRequestClOrdId

def decode (bytes : List UInt8) : Option (CpClearAllBreachesRequestMessage × List UInt8) := do
  let (clOrdIdCpClearAllBreachesRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  pure ({ clOrdIdCpClearAllBreachesRequestClOrdId }, bytes)

@[simp] theorem encode_length (message : CpClearAllBreachesRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CpClearAllBreachesRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearAllBreachesRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CpClearAllBreachesRequestMessage

/-- Cp Clear All Breaches By Efid Or Underlier Request Message: 30 bytes -/
structure CpClearAllBreachesByEfidOrUnderlierRequestMessage where
  clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId : Alpha 20
  underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional : Alpha 6
  efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional : Alpha 4
  deriving DecidableEq, Repr

namespace CpClearAllBreachesByEfidOrUnderlierRequestMessage

def encode (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId
    ++ (Alpha.encode message.underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional))

def decode (bytes : List UInt8) : Option (CpClearAllBreachesByEfidOrUnderlierRequestMessage × List UInt8) := do
  let (clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId, underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional, efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional }, bytes)

@[simp] theorem encode_length (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CpClearAllBreachesByEfidOrUnderlierRequestMessage

/-- Active Risk Acknowledge All Request Message: 30 bytes -/
structure ActiveRiskAcknowledgeAllRequestMessage where
  clOrdIdActiveRiskAcknowledgeAllRequestClOrdId : Alpha 20
  underlierActiveRiskAcknowledgeAllRequestUnderlier : Alpha 6
  efidActiveRiskAcknowledgeAllRequestEfid : Alpha 4
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgeAllRequestMessage

def encode (message : ActiveRiskAcknowledgeAllRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskAcknowledgeAllRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskAcknowledgeAllRequestUnderlier
    ++ (Alpha.encode message.efidActiveRiskAcknowledgeAllRequestEfid))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgeAllRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskAcknowledgeAllRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskAcknowledgeAllRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskAcknowledgeAllRequestEfid, bytes) ← Alpha.decode 4 bytes
  pure ({ clOrdIdActiveRiskAcknowledgeAllRequestClOrdId, underlierActiveRiskAcknowledgeAllRequestUnderlier, efidActiveRiskAcknowledgeAllRequestEfid }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgeAllRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgeAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgeAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ActiveRiskAcknowledgeAllRequestMessage

/-- Active Risk Threshold State Message: 38 bytes -/
structure ActiveRiskThresholdStateMessage where
  clordidOptional : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  thresholdQuantity : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdStateMessage

def encode (message : ActiveRiskThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 4 message.unackedQuantity))))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlier, efid, thresholdQuantity, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdStateMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdStateMessage

/-- Active Risk Threshold Change Rejected Message: 36 bytes -/
structure ActiveRiskThresholdChangeRejectedMessage where
  clOrdIdActiveRiskThresholdChangeRejectedClOrdId : Alpha 20
  underlierActiveRiskThresholdChangeRejectedUnderlierOptional : Alpha 6
  efidActiveRiskThresholdChangeRejectedEfidOptional : Alpha 4
  thresholdQuantity : BitVec 32
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdChangeRejectedMessage

def encode (message : ActiveRiskThresholdChangeRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskThresholdChangeRejectedClOrdId
    ++ (Alpha.encode message.underlierActiveRiskThresholdChangeRejectedUnderlierOptional
    ++ (Alpha.encode message.efidActiveRiskThresholdChangeRejectedEfidOptional
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdChangeRejectedMessage × List UInt8) := do
  let (clOrdIdActiveRiskThresholdChangeRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskThresholdChangeRejectedUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskThresholdChangeRejectedEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdActiveRiskThresholdChangeRejectedClOrdId, underlierActiveRiskThresholdChangeRejectedUnderlierOptional, efidActiveRiskThresholdChangeRejectedEfidOptional, thresholdQuantity, rejectReason }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdChangeRejectedMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdChangeRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdChangeRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdChangeRejectedMessage

/-- Active Risk Acknowledged Message: 38 bytes -/
structure ActiveRiskAcknowledgedMessage where
  clordid : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  quantity : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgedMessage

def encode (message : ActiveRiskAcknowledgedMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.unackedQuantity))))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgedMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlier, efid, quantity, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgedMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgedMessage

/-- Active Risk Acknowledge Rejected Message: 36 bytes -/
structure ActiveRiskAcknowledgeRejectedMessage where
  clOrdIdActiveRiskAcknowledgeRejectedClOrdId : Alpha 20
  underlierActiveRiskAcknowledgeRejectedUnderlier : Alpha 6
  efidActiveRiskAcknowledgeRejectedEfid : Alpha 4
  thresholdQuantity : BitVec 32
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgeRejectedMessage

def encode (message : ActiveRiskAcknowledgeRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskAcknowledgeRejectedClOrdId
    ++ (Alpha.encode message.underlierActiveRiskAcknowledgeRejectedUnderlier
    ++ (Alpha.encode message.efidActiveRiskAcknowledgeRejectedEfid
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgeRejectedMessage × List UInt8) := do
  let (clOrdIdActiveRiskAcknowledgeRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskAcknowledgeRejectedUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskAcknowledgeRejectedEfid, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdActiveRiskAcknowledgeRejectedClOrdId, underlierActiveRiskAcknowledgeRejectedUnderlier, efidActiveRiskAcknowledgeRejectedEfid, thresholdQuantity, rejectReason }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgeRejectedMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgeRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgeRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgeRejectedMessage

/-- Active Risk Quantity Update Notification Message: 67 bytes -/
structure ActiveRiskQuantityUpdateNotificationMessage where
  sendingTime : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  trdMatchId : BitVec 64
  efid : Alpha 4
  underlier : Alpha 6
  optionSecurityId : Alpha 8
  side : Side
  lastPx : BitVec 64
  lastQty : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskQuantityUpdateNotificationMessage

def encode (message : ActiveRiskQuantityUpdateNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.trdMatchId
    ++ (Alpha.encode message.efid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.optionSecurityId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 4 message.unackedQuantity))))))))))

def decode (bytes : List UInt8) : Option (ActiveRiskQuantityUpdateNotificationMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (optionSecurityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ sendingTime, transactTime, orderId, trdMatchId, efid, underlier, optionSecurityId, side, lastPx, lastQty, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskQuantityUpdateNotificationMessage) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : ActiveRiskQuantityUpdateNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskQuantityUpdateNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskQuantityUpdateNotificationMessage

/-- Cp Volume Threshold State Message: 44 bytes -/
structure CpVolumeThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  volume : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpVolumeThresholdStateMessage

def encode (message : CpVolumeThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpVolumeThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, volume, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpVolumeThresholdStateMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpVolumeThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpVolumeThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpVolumeThresholdStateMessage

/-- Cp Executed Notional Threshold State Message: 44 bytes -/
structure CpExecutedNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpExecutedNotionalThresholdStateMessage

def encode (message : CpExecutedNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpExecutedNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpExecutedNotionalThresholdStateMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpExecutedNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpExecutedNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpExecutedNotionalThresholdStateMessage

/-- Cp Total Executions Threshold State Message: 40 bytes -/
structure CpTotalExecutionsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  totalExecutions : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpTotalExecutionsThresholdStateMessage

def encode (message : CpTotalExecutionsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.totalExecutions
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpTotalExecutionsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (totalExecutions, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, totalExecutions, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpTotalExecutionsThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpTotalExecutionsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpTotalExecutionsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpTotalExecutionsThresholdStateMessage

/-- Cp Percent Outstanding Contracts Threshold State Message: 38 bytes -/
structure CpPercentOutstandingContractsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  percent : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpPercentOutstandingContractsThresholdStateMessage

def encode (message : CpPercentOutstandingContractsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 4 message.percent
    ++ (encodeUInt 4 message.periodInMilliSeconds))))

def decode (bytes : List UInt8) : Option (CpPercentOutstandingContractsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (percent, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, percent, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpPercentOutstandingContractsThresholdStateMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpPercentOutstandingContractsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpPercentOutstandingContractsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpPercentOutstandingContractsThresholdStateMessage

/-- Cp Breach Count Threshold State Message: 40 bytes -/
structure CpBreachCountThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  count : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpBreachCountThresholdStateMessage

def encode (message : CpBreachCountThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.count
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpBreachCountThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, count, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpBreachCountThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpBreachCountThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpBreachCountThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpBreachCountThresholdStateMessage

/-- Manual Cp Breach Trigger Pending Message: 32 bytes -/
structure ManualCpBreachTriggerPendingMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerPendingMessage

def encode (message : ManualCpBreachTriggerPendingMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId)))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerPendingMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerPendingMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerPendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerPendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerPendingMessage

/-- Manual Cp Breach Trigger Done Message: 44 bytes -/
structure ManualCpBreachTriggerDoneMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  breachId : BitVec 64
  totalAffectedOrders : BitVec 32
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerDoneMessage

def encode (message : ManualCpBreachTriggerDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.breachId
    ++ (encodeUInt 4 message.totalAffectedOrders)))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (breachId, bytes) ← decodeUInt 8 bytes
  let (totalAffectedOrders, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, breachId, totalAffectedOrders }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerDoneMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerDoneMessage

/-- Risk Threshold Update Rejected Message: 23 bytes -/
structure RiskThresholdUpdateRejectedMessage where
  clOrdIdRiskThresholdUpdateRejectedClOrdId : Alpha 20
  riskType : BitVec 8
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace RiskThresholdUpdateRejectedMessage

def encode (message : RiskThresholdUpdateRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdRiskThresholdUpdateRejectedClOrdId
    ++ (encodeUInt 1 message.riskType
    ++ (encodeUInt 2 message.rejectReason))

def decode (bytes : List UInt8) : Option (RiskThresholdUpdateRejectedMessage × List UInt8) := do
  let (clOrdIdRiskThresholdUpdateRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (riskType, bytes) ← decodeUInt 1 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdRiskThresholdUpdateRejectedClOrdId, riskType, rejectReason }, bytes)

@[simp] theorem encode_length (message : RiskThresholdUpdateRejectedMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskThresholdUpdateRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskThresholdUpdateRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskThresholdUpdateRejectedMessage

/-- Passive Risk Threshold Notification Message: 30 bytes -/
structure PassiveRiskThresholdNotificationMessage where
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  ruleType : BitVec 8
  latestPercentage : BitVec 8
  breachIdOptional : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PassiveRiskThresholdNotificationMessage

def encode (message : PassiveRiskThresholdNotificationMessage) : List UInt8 :=
  Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.ruleType
    ++ (encodeUInt 1 message.latestPercentage
    ++ (encodeUInt 8 message.breachIdOptional
    ++ (encodeUInt 8 message.transactTime))))))

def decode (bytes : List UInt8) : Option (PassiveRiskThresholdNotificationMessage × List UInt8) := do
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (ruleType, bytes) ← decodeUInt 1 bytes
  let (latestPercentage, bytes) ← decodeUInt 1 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ underlierOptional, efidOptional, riskGroupId, ruleType, latestPercentage, breachIdOptional, transactTime }, bytes)

@[simp] theorem encode_length (message : PassiveRiskThresholdNotificationMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PassiveRiskThresholdNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PassiveRiskThresholdNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PassiveRiskThresholdNotificationMessage

/-- Single Order Allow Iso Orders State Message: 33 bytes -/
structure SingleOrderAllowIsoOrdersStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowIsoOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowIsoOrdersStateMessage

def encode (message : SingleOrderAllowIsoOrdersStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowIsoOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowIsoOrdersStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowIsoOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, allowIsoOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowIsoOrdersStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowIsoOrdersStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowIsoOrdersStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowIsoOrdersStateMessage

/-- Single Order Allow Orders In Crossed Market State Message: 33 bytes -/
structure SingleOrderAllowOrdersInCrossedMarketStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowOrdersInCrossedMarketStateMessage

def encode (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowOrdersInCrossedMarketStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, allowOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowOrdersInCrossedMarketStateMessage

/-- Single Order Max Notional Threshold State Message: 40 bytes -/
structure SingleOrderMaxNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxNotionalInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace SingleOrderMaxNotionalThresholdStateMessage

def encode (message : SingleOrderMaxNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.maxNotionalInDollars))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxNotionalInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxNotionalInDollars }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxNotionalThresholdStateMessage

/-- Single Order Max Contracts Threshold State Message: 36 bytes -/
structure SingleOrderMaxContractsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleOrderMaxContractsThresholdStateMessage

def encode (message : SingleOrderMaxContractsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxContracts))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxContractsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxContracts, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxContracts }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxContractsThresholdStateMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxContractsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxContractsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxContractsThresholdStateMessage

/-- Single Order Allow Market Orders State Message: 33 bytes -/
structure SingleOrderAllowMarketOrdersStateMessage where
  clOrdIdSingleOrderAllowMarketOrdersStateClOrdIdOptional : Alpha 20
  underlierSingleOrderAllowMarketOrdersStateUnderlierOptional : Alpha 6
  efidSingleOrderAllowMarketOrdersStateEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  marketOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowMarketOrdersStateMessage

def encode (message : SingleOrderAllowMarketOrdersStateMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowMarketOrdersStateClOrdIdOptional
    ++ (Alpha.encode message.underlierSingleOrderAllowMarketOrdersStateUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowMarketOrdersStateEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.marketOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowMarketOrdersStateMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowMarketOrdersStateClOrdIdOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowMarketOrdersStateUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowMarketOrdersStateEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (marketOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowMarketOrdersStateClOrdIdOptional, underlierSingleOrderAllowMarketOrdersStateUnderlierOptional, efidSingleOrderAllowMarketOrdersStateEfidOptional, riskGroupId, marketOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowMarketOrdersStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowMarketOrdersStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowMarketOrdersStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowMarketOrdersStateMessage

/-- Single Order Restricted Underlier State Message: 33 bytes -/
structure SingleOrderRestrictedUnderlierStateMessage where
  clOrdIdSingleOrderRestrictedUnderlierStateClOrdIdOptional : Alpha 20
  underlierSingleOrderRestrictedUnderlierStateUnderlier : Alpha 6
  efidSingleOrderRestrictedUnderlierStateEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  restricted : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderRestrictedUnderlierStateMessage

def encode (message : SingleOrderRestrictedUnderlierStateMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderRestrictedUnderlierStateClOrdIdOptional
    ++ (Alpha.encode message.underlierSingleOrderRestrictedUnderlierStateUnderlier
    ++ (Alpha.encode message.efidSingleOrderRestrictedUnderlierStateEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.restricted))))

def decode (bytes : List UInt8) : Option (SingleOrderRestrictedUnderlierStateMessage × List UInt8) := do
  let (clOrdIdSingleOrderRestrictedUnderlierStateClOrdIdOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderRestrictedUnderlierStateUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderRestrictedUnderlierStateEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (restricted, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderRestrictedUnderlierStateClOrdIdOptional, underlierSingleOrderRestrictedUnderlierStateUnderlier, efidSingleOrderRestrictedUnderlierStateEfidOptional, riskGroupId, restricted }, bytes)

@[simp] theorem encode_length (message : SingleOrderRestrictedUnderlierStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderRestrictedUnderlierStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderRestrictedUnderlierStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderRestrictedUnderlierStateMessage

/-- Risk Settings Query Done Message: 24 bytes -/
structure RiskSettingsQueryDoneMessage where
  clordid : Alpha 20
  numberMsgsSent : BitVec 32
  deriving DecidableEq, Repr

namespace RiskSettingsQueryDoneMessage

def encode (message : RiskSettingsQueryDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 4 message.numberMsgsSent)

def decode (bytes : List UInt8) : Option (RiskSettingsQueryDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (numberMsgsSent, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, numberMsgsSent }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryDoneMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskSettingsQueryDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskSettingsQueryDoneMessage

/-- Risk Settings Query Rejected Message: 22 bytes -/
structure RiskSettingsQueryRejectedMessage where
  clOrdIdRiskSettingsQueryRejectedClOrdId : Alpha 20
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace RiskSettingsQueryRejectedMessage

def encode (message : RiskSettingsQueryRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdRiskSettingsQueryRejectedClOrdId
    ++ (encodeUInt 2 message.rejectReason)

def decode (bytes : List UInt8) : Option (RiskSettingsQueryRejectedMessage × List UInt8) := do
  let (clOrdIdRiskSettingsQueryRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdRiskSettingsQueryRejectedClOrdId, rejectReason }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryRejectedMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskSettingsQueryRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskSettingsQueryRejectedMessage

/-- Manual Cp Breach Trigger Rejected Message: 34 bytes -/
structure ManualCpBreachTriggerRejectedMessage where
  clOrdIdManualCpBreachTriggerRejectedClOrdId : Alpha 20
  underlierManualCpBreachTriggerRejectedUnderlierOptional : Alpha 6
  efidManualCpBreachTriggerRejectedEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerRejectedMessage

def encode (message : ManualCpBreachTriggerRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdManualCpBreachTriggerRejectedClOrdId
    ++ (Alpha.encode message.underlierManualCpBreachTriggerRejectedUnderlierOptional
    ++ (Alpha.encode message.efidManualCpBreachTriggerRejectedEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerRejectedMessage × List UInt8) := do
  let (clOrdIdManualCpBreachTriggerRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierManualCpBreachTriggerRejectedUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidManualCpBreachTriggerRejectedEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdManualCpBreachTriggerRejectedClOrdId, underlierManualCpBreachTriggerRejectedUnderlierOptional, efidManualCpBreachTriggerRejectedEfidOptional, riskGroupId, rejectReason }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerRejectedMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerRejectedMessage

/-- Breach Clear Rejected Message: 30 bytes -/
structure BreachClearRejectedMessage where
  clOrdIdBreachClearRejectedClOrdId : Alpha 20
  breachIdOptional : BitVec 64
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace BreachClearRejectedMessage

def encode (message : BreachClearRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdBreachClearRejectedClOrdId
    ++ (encodeUInt 8 message.breachIdOptional
    ++ (encodeUInt 2 message.rejectReason))

def decode (bytes : List UInt8) : Option (BreachClearRejectedMessage × List UInt8) := do
  let (clOrdIdBreachClearRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdBreachClearRejectedClOrdId, breachIdOptional, rejectReason }, bytes)

@[simp] theorem encode_length (message : BreachClearRejectedMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearRejectedMessage

/-- Breach Cleared Message: 28 bytes -/
structure BreachClearedMessage where
  clordidOptional : Alpha 20
  breachIdOptional : BitVec 64
  deriving DecidableEq, Repr

namespace BreachClearedMessage

def encode (message : BreachClearedMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (encodeUInt 8 message.breachIdOptional)

def decode (bytes : List UInt8) : Option (BreachClearedMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, breachIdOptional }, bytes)

@[simp] theorem encode_length (message : BreachClearedMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearedMessage

/-- Breach Clear All Accepted Message: 20 bytes -/
structure BreachClearAllAcceptedMessage where
  clOrdIdBreachClearAllAcceptedClOrdId : Alpha 20
  deriving DecidableEq, Repr

namespace BreachClearAllAcceptedMessage

def encode (message : BreachClearAllAcceptedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdBreachClearAllAcceptedClOrdId

def decode (bytes : List UInt8) : Option (BreachClearAllAcceptedMessage × List UInt8) := do
  let (clOrdIdBreachClearAllAcceptedClOrdId, bytes) ← Alpha.decode 20 bytes
  pure ({ clOrdIdBreachClearAllAcceptedClOrdId }, bytes)

@[simp] theorem encode_length (message : BreachClearAllAcceptedMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BreachClearAllAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearAllAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BreachClearAllAcceptedMessage

/-- Breach Clear All Rejected Message: 22 bytes -/
structure BreachClearAllRejectedMessage where
  clOrdIdBreachClearAllRejectedClOrdId : Alpha 20
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace BreachClearAllRejectedMessage

def encode (message : BreachClearAllRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdBreachClearAllRejectedClOrdId
    ++ (encodeUInt 2 message.rejectReason)

def decode (bytes : List UInt8) : Option (BreachClearAllRejectedMessage × List UInt8) := do
  let (clOrdIdBreachClearAllRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdBreachClearAllRejectedClOrdId, rejectReason }, bytes)

@[simp] theorem encode_length (message : BreachClearAllRejectedMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearAllRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearAllRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearAllRejectedMessage

/-- Breach Clear All By Efid Or Underlier Accepted Message: 30 bytes -/
structure BreachClearAllByEfidOrUnderlierAcceptedMessage where
  clOrdIdBreachClearAllByEfidOrUnderlierAcceptedClOrdId : Alpha 20
  underlierBreachClearAllByEfidOrUnderlierAcceptedUnderlierOptional : Alpha 6
  efidBreachClearAllByEfidOrUnderlierAcceptedEfidOptional : Alpha 4
  deriving DecidableEq, Repr

namespace BreachClearAllByEfidOrUnderlierAcceptedMessage

def encode (message : BreachClearAllByEfidOrUnderlierAcceptedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdBreachClearAllByEfidOrUnderlierAcceptedClOrdId
    ++ (Alpha.encode message.underlierBreachClearAllByEfidOrUnderlierAcceptedUnderlierOptional
    ++ (Alpha.encode message.efidBreachClearAllByEfidOrUnderlierAcceptedEfidOptional))

def decode (bytes : List UInt8) : Option (BreachClearAllByEfidOrUnderlierAcceptedMessage × List UInt8) := do
  let (clOrdIdBreachClearAllByEfidOrUnderlierAcceptedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierBreachClearAllByEfidOrUnderlierAcceptedUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidBreachClearAllByEfidOrUnderlierAcceptedEfidOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ clOrdIdBreachClearAllByEfidOrUnderlierAcceptedClOrdId, underlierBreachClearAllByEfidOrUnderlierAcceptedUnderlierOptional, efidBreachClearAllByEfidOrUnderlierAcceptedEfidOptional }, bytes)

@[simp] theorem encode_length (message : BreachClearAllByEfidOrUnderlierAcceptedMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BreachClearAllByEfidOrUnderlierAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearAllByEfidOrUnderlierAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BreachClearAllByEfidOrUnderlierAcceptedMessage

/-- Breach Clear All By Efid Or Underlier Rejected Message: 32 bytes -/
structure BreachClearAllByEfidOrUnderlierRejectedMessage where
  clOrdIdBreachClearAllByEfidOrUnderlierRejectedClOrdId : Alpha 20
  underlierBreachClearAllByEfidOrUnderlierRejectedUnderlierOptional : Alpha 6
  efidBreachClearAllByEfidOrUnderlierRejectedEfidOptional : Alpha 4
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace BreachClearAllByEfidOrUnderlierRejectedMessage

def encode (message : BreachClearAllByEfidOrUnderlierRejectedMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdBreachClearAllByEfidOrUnderlierRejectedClOrdId
    ++ (Alpha.encode message.underlierBreachClearAllByEfidOrUnderlierRejectedUnderlierOptional
    ++ (Alpha.encode message.efidBreachClearAllByEfidOrUnderlierRejectedEfidOptional
    ++ (encodeUInt 2 message.rejectReason)))

def decode (bytes : List UInt8) : Option (BreachClearAllByEfidOrUnderlierRejectedMessage × List UInt8) := do
  let (clOrdIdBreachClearAllByEfidOrUnderlierRejectedClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierBreachClearAllByEfidOrUnderlierRejectedUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidBreachClearAllByEfidOrUnderlierRejectedEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clOrdIdBreachClearAllByEfidOrUnderlierRejectedClOrdId, underlierBreachClearAllByEfidOrUnderlierRejectedUnderlierOptional, efidBreachClearAllByEfidOrUnderlierRejectedEfidOptional, rejectReason }, bytes)

@[simp] theorem encode_length (message : BreachClearAllByEfidOrUnderlierRejectedMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearAllByEfidOrUnderlierRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearAllByEfidOrUnderlierRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearAllByEfidOrUnderlierRejectedMessage

/-- Cp Gross Notional Threshold State Message: 40 bytes -/
structure CpGrossNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpGrossNotionalThresholdStateMessage

def encode (message : CpGrossNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpGrossNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpGrossNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpGrossNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpGrossNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpGrossNotionalThresholdStateMessage

/-- Cp Market Order Gross Notional Threshold State Message: 40 bytes -/
structure CpMarketOrderGrossNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderGrossNotionalThresholdStateMessage

def encode (message : CpMarketOrderGrossNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderGrossNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderGrossNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderGrossNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderGrossNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderGrossNotionalThresholdStateMessage

/-- Cp Net Notional Threshold State Message: 40 bytes -/
structure CpNetNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpNetNotionalThresholdStateMessage

def encode (message : CpNetNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpNetNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpNetNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpNetNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpNetNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpNetNotionalThresholdStateMessage

/-- Cp Market Order Net Notional Threshold State Message: 40 bytes -/
structure CpMarketOrderNetNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderNetNotionalThresholdStateMessage

def encode (message : CpMarketOrderNetNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderNetNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderNetNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderNetNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderNetNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderNetNotionalThresholdStateMessage

/-- Cp Duplicate Order Threshold State Message: 41 bytes -/
structure CpDuplicateOrderThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxDupOrders : BitVec 32
  useOrderPriceInDupCheck : BitVec 8
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpDuplicateOrderThresholdStateMessage

def encode (message : CpDuplicateOrderThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxDupOrders
    ++ (encodeUInt 1 message.useOrderPriceInDupCheck
    ++ (encodeUInt 4 message.periodInMilliSeconds))))))

def decode (bytes : List UInt8) : Option (CpDuplicateOrderThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxDupOrders, bytes) ← decodeUInt 4 bytes
  let (useOrderPriceInDupCheck, bytes) ← decodeUInt 1 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxDupOrders, useOrderPriceInDupCheck, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpDuplicateOrderThresholdStateMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpDuplicateOrderThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpDuplicateOrderThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpDuplicateOrderThresholdStateMessage

/-- Cp Order Rate Threshold State Message: 40 bytes -/
structure CpOrderRateThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxOrderMsgs : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpOrderRateThresholdStateMessage

def encode (message : CpOrderRateThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxOrderMsgs
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpOrderRateThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxOrderMsgs, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxOrderMsgs, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpOrderRateThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpOrderRateThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpOrderRateThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpOrderRateThresholdStateMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | riskSettingsQueryMessage (message : RiskSettingsQueryMessage) -- 1
  | activeRiskThresholdChangeRequestMessage (message : ActiveRiskThresholdChangeRequestMessage) -- 2
  | activeRiskAcknowledgementRequestMessage (message : ActiveRiskAcknowledgementRequestMessage) -- 3
  | cpVolumeThresholdChangeRequestMessage (message : CpVolumeThresholdChangeRequestMessage) -- 4
  | cpExecutedNotionalThresholdChangeRequestMessage (message : CpExecutedNotionalThresholdChangeRequestMessage) -- 5
  | cpTotalExecutionsThresholdChangeRequestMessage (message : CpTotalExecutionsThresholdChangeRequestMessage) -- 6
  | cpPercentOutstandingContractsThresholdChangeRequestMessage (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) -- 7
  | cpBreachCountThresholdChangeRequestMessage (message : CpBreachCountThresholdChangeRequestMessage) -- 8
  | manualCpBreachTriggerRequestMessage (message : ManualCpBreachTriggerRequestMessage) -- 9
  | cpClearBreachRequestMessage (message : CpClearBreachRequestMessage) -- 10
  | singleOrderAllowIsoOrdersChangeRequestMessage (message : SingleOrderAllowIsoOrdersChangeRequestMessage) -- 11
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) -- 12
  | singleOrderMaxNotionalChangeRequestMessage (message : SingleOrderMaxNotionalChangeRequestMessage) -- 13
  | singleOrderMaxContractsChangeRequestMessage (message : SingleOrderMaxContractsChangeRequestMessage) -- 14
  | singleOrderAllowMarketOrdersChangeRequestMessage (message : SingleOrderAllowMarketOrdersChangeRequestMessage) -- 15
  | singleOrderRestrictedUnderlierChangeRequestMessage (message : SingleOrderRestrictedUnderlierChangeRequestMessage) -- 16
  | cpGrossNotionalThresholdChangeRequestMessage (message : CpGrossNotionalThresholdChangeRequestMessage) -- 18
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) -- 19
  | cpNetNotionalThresholdChangeRequestMessage (message : CpNetNotionalThresholdChangeRequestMessage) -- 20
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) -- 21
  | cpDuplicateOrderThresholdChangeRequestMessage (message : CpDuplicateOrderThresholdChangeRequestMessage) -- 22
  | cpOrderRateThresholdChangeRequestMessage (message : CpOrderRateThresholdChangeRequestMessage) -- 23
  | cpClearAllBreachesRequestMessage (message : CpClearAllBreachesRequestMessage) -- 24
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) -- 25
  | activeRiskAcknowledgeAllRequestMessage (message : ActiveRiskAcknowledgeAllRequestMessage) -- 26
  | activeRiskThresholdStateMessage (message : ActiveRiskThresholdStateMessage) -- 30
  | activeRiskThresholdChangeRejectedMessage (message : ActiveRiskThresholdChangeRejectedMessage) -- 31
  | activeRiskAcknowledgedMessage (message : ActiveRiskAcknowledgedMessage) -- 32
  | activeRiskAcknowledgeRejectedMessage (message : ActiveRiskAcknowledgeRejectedMessage) -- 33
  | activeRiskQuantityUpdateNotificationMessage (message : ActiveRiskQuantityUpdateNotificationMessage) -- 34
  | cpVolumeThresholdStateMessage (message : CpVolumeThresholdStateMessage) -- 35
  | cpExecutedNotionalThresholdStateMessage (message : CpExecutedNotionalThresholdStateMessage) -- 36
  | cpTotalExecutionsThresholdStateMessage (message : CpTotalExecutionsThresholdStateMessage) -- 37
  | cpPercentOutstandingContractsThresholdStateMessage (message : CpPercentOutstandingContractsThresholdStateMessage) -- 38
  | cpBreachCountThresholdStateMessage (message : CpBreachCountThresholdStateMessage) -- 39
  | manualCpBreachTriggerPendingMessage (message : ManualCpBreachTriggerPendingMessage) -- 40
  | manualCpBreachTriggerDoneMessage (message : ManualCpBreachTriggerDoneMessage) -- 41
  | riskThresholdUpdateRejectedMessage (message : RiskThresholdUpdateRejectedMessage) -- 42
  | passiveRiskThresholdNotificationMessage (message : PassiveRiskThresholdNotificationMessage) -- 43
  | singleOrderAllowIsoOrdersStateMessage (message : SingleOrderAllowIsoOrdersStateMessage) -- 44
  | singleOrderAllowOrdersInCrossedMarketStateMessage (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) -- 45
  | singleOrderMaxNotionalThresholdStateMessage (message : SingleOrderMaxNotionalThresholdStateMessage) -- 46
  | singleOrderMaxContractsThresholdStateMessage (message : SingleOrderMaxContractsThresholdStateMessage) -- 47
  | singleOrderAllowMarketOrdersStateMessage (message : SingleOrderAllowMarketOrdersStateMessage) -- 66
  | singleOrderRestrictedUnderlierStateMessage (message : SingleOrderRestrictedUnderlierStateMessage) -- 67
  | riskSettingsQueryDoneMessage (message : RiskSettingsQueryDoneMessage) -- 48
  | riskSettingsQueryRejectedMessage (message : RiskSettingsQueryRejectedMessage) -- 49
  | manualCpBreachTriggerRejectedMessage (message : ManualCpBreachTriggerRejectedMessage) -- 50
  | breachClearRejectedMessage (message : BreachClearRejectedMessage) -- 51
  | breachClearedMessage (message : BreachClearedMessage) -- 52
  | breachClearAllAcceptedMessage (message : BreachClearAllAcceptedMessage) -- 53
  | breachClearAllRejectedMessage (message : BreachClearAllRejectedMessage) -- 69
  | breachClearAllByEfidOrUnderlierAcceptedMessage (message : BreachClearAllByEfidOrUnderlierAcceptedMessage) -- 54
  | breachClearAllByEfidOrUnderlierRejectedMessage (message : BreachClearAllByEfidOrUnderlierRejectedMessage) -- 68
  | cpGrossNotionalThresholdStateMessage (message : CpGrossNotionalThresholdStateMessage) -- 60
  | cpMarketOrderGrossNotionalThresholdStateMessage (message : CpMarketOrderGrossNotionalThresholdStateMessage) -- 61
  | cpNetNotionalThresholdStateMessage (message : CpNetNotionalThresholdStateMessage) -- 62
  | cpMarketOrderNetNotionalThresholdStateMessage (message : CpMarketOrderNetNotionalThresholdStateMessage) -- 63
  | cpDuplicateOrderThresholdStateMessage (message : CpDuplicateOrderThresholdStateMessage) -- 64
  | cpOrderRateThresholdStateMessage (message : CpOrderRateThresholdStateMessage) -- 65
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .riskSettingsQueryMessage _ => 1
  | .activeRiskThresholdChangeRequestMessage _ => 2
  | .activeRiskAcknowledgementRequestMessage _ => 3
  | .cpVolumeThresholdChangeRequestMessage _ => 4
  | .cpExecutedNotionalThresholdChangeRequestMessage _ => 5
  | .cpTotalExecutionsThresholdChangeRequestMessage _ => 6
  | .cpPercentOutstandingContractsThresholdChangeRequestMessage _ => 7
  | .cpBreachCountThresholdChangeRequestMessage _ => 8
  | .manualCpBreachTriggerRequestMessage _ => 9
  | .cpClearBreachRequestMessage _ => 10
  | .singleOrderAllowIsoOrdersChangeRequestMessage _ => 11
  | .singleOrderAllowOrdersInCrossedMarketChangeRequestMessage _ => 12
  | .singleOrderMaxNotionalChangeRequestMessage _ => 13
  | .singleOrderMaxContractsChangeRequestMessage _ => 14
  | .singleOrderAllowMarketOrdersChangeRequestMessage _ => 15
  | .singleOrderRestrictedUnderlierChangeRequestMessage _ => 16
  | .cpGrossNotionalThresholdChangeRequestMessage _ => 18
  | .cpMarketOrderGrossNotionalThresholdChangeRequestMessage _ => 19
  | .cpNetNotionalThresholdChangeRequestMessage _ => 20
  | .cpMarketOrderNetNotionalThresholdChangeRequestMessage _ => 21
  | .cpDuplicateOrderThresholdChangeRequestMessage _ => 22
  | .cpOrderRateThresholdChangeRequestMessage _ => 23
  | .cpClearAllBreachesRequestMessage _ => 24
  | .cpClearAllBreachesByEfidOrUnderlierRequestMessage _ => 25
  | .activeRiskAcknowledgeAllRequestMessage _ => 26
  | .activeRiskThresholdStateMessage _ => 30
  | .activeRiskThresholdChangeRejectedMessage _ => 31
  | .activeRiskAcknowledgedMessage _ => 32
  | .activeRiskAcknowledgeRejectedMessage _ => 33
  | .activeRiskQuantityUpdateNotificationMessage _ => 34
  | .cpVolumeThresholdStateMessage _ => 35
  | .cpExecutedNotionalThresholdStateMessage _ => 36
  | .cpTotalExecutionsThresholdStateMessage _ => 37
  | .cpPercentOutstandingContractsThresholdStateMessage _ => 38
  | .cpBreachCountThresholdStateMessage _ => 39
  | .manualCpBreachTriggerPendingMessage _ => 40
  | .manualCpBreachTriggerDoneMessage _ => 41
  | .riskThresholdUpdateRejectedMessage _ => 42
  | .passiveRiskThresholdNotificationMessage _ => 43
  | .singleOrderAllowIsoOrdersStateMessage _ => 44
  | .singleOrderAllowOrdersInCrossedMarketStateMessage _ => 45
  | .singleOrderMaxNotionalThresholdStateMessage _ => 46
  | .singleOrderMaxContractsThresholdStateMessage _ => 47
  | .singleOrderAllowMarketOrdersStateMessage _ => 66
  | .singleOrderRestrictedUnderlierStateMessage _ => 67
  | .riskSettingsQueryDoneMessage _ => 48
  | .riskSettingsQueryRejectedMessage _ => 49
  | .manualCpBreachTriggerRejectedMessage _ => 50
  | .breachClearRejectedMessage _ => 51
  | .breachClearedMessage _ => 52
  | .breachClearAllAcceptedMessage _ => 53
  | .breachClearAllRejectedMessage _ => 69
  | .breachClearAllByEfidOrUnderlierAcceptedMessage _ => 54
  | .breachClearAllByEfidOrUnderlierRejectedMessage _ => 68
  | .cpGrossNotionalThresholdStateMessage _ => 60
  | .cpMarketOrderGrossNotionalThresholdStateMessage _ => 61
  | .cpNetNotionalThresholdStateMessage _ => 62
  | .cpMarketOrderNetNotionalThresholdStateMessage _ => 63
  | .cpDuplicateOrderThresholdStateMessage _ => 64
  | .cpOrderRateThresholdStateMessage _ => 65

def encode : Payload → List UInt8
  | .riskSettingsQueryMessage message => RiskSettingsQueryMessage.encode message
  | .activeRiskThresholdChangeRequestMessage message => ActiveRiskThresholdChangeRequestMessage.encode message
  | .activeRiskAcknowledgementRequestMessage message => ActiveRiskAcknowledgementRequestMessage.encode message
  | .cpVolumeThresholdChangeRequestMessage message => CpVolumeThresholdChangeRequestMessage.encode message
  | .cpExecutedNotionalThresholdChangeRequestMessage message => CpExecutedNotionalThresholdChangeRequestMessage.encode message
  | .cpTotalExecutionsThresholdChangeRequestMessage message => CpTotalExecutionsThresholdChangeRequestMessage.encode message
  | .cpPercentOutstandingContractsThresholdChangeRequestMessage message => CpPercentOutstandingContractsThresholdChangeRequestMessage.encode message
  | .cpBreachCountThresholdChangeRequestMessage message => CpBreachCountThresholdChangeRequestMessage.encode message
  | .manualCpBreachTriggerRequestMessage message => ManualCpBreachTriggerRequestMessage.encode message
  | .cpClearBreachRequestMessage message => CpClearBreachRequestMessage.encode message
  | .singleOrderAllowIsoOrdersChangeRequestMessage message => SingleOrderAllowIsoOrdersChangeRequestMessage.encode message
  | .singleOrderAllowOrdersInCrossedMarketChangeRequestMessage message => SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode message
  | .singleOrderMaxNotionalChangeRequestMessage message => SingleOrderMaxNotionalChangeRequestMessage.encode message
  | .singleOrderMaxContractsChangeRequestMessage message => SingleOrderMaxContractsChangeRequestMessage.encode message
  | .singleOrderAllowMarketOrdersChangeRequestMessage message => SingleOrderAllowMarketOrdersChangeRequestMessage.encode message
  | .singleOrderRestrictedUnderlierChangeRequestMessage message => SingleOrderRestrictedUnderlierChangeRequestMessage.encode message
  | .cpGrossNotionalThresholdChangeRequestMessage message => CpGrossNotionalThresholdChangeRequestMessage.encode message
  | .cpMarketOrderGrossNotionalThresholdChangeRequestMessage message => CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode message
  | .cpNetNotionalThresholdChangeRequestMessage message => CpNetNotionalThresholdChangeRequestMessage.encode message
  | .cpMarketOrderNetNotionalThresholdChangeRequestMessage message => CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode message
  | .cpDuplicateOrderThresholdChangeRequestMessage message => CpDuplicateOrderThresholdChangeRequestMessage.encode message
  | .cpOrderRateThresholdChangeRequestMessage message => CpOrderRateThresholdChangeRequestMessage.encode message
  | .cpClearAllBreachesRequestMessage message => CpClearAllBreachesRequestMessage.encode message
  | .cpClearAllBreachesByEfidOrUnderlierRequestMessage message => CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode message
  | .activeRiskAcknowledgeAllRequestMessage message => ActiveRiskAcknowledgeAllRequestMessage.encode message
  | .activeRiskThresholdStateMessage message => ActiveRiskThresholdStateMessage.encode message
  | .activeRiskThresholdChangeRejectedMessage message => ActiveRiskThresholdChangeRejectedMessage.encode message
  | .activeRiskAcknowledgedMessage message => ActiveRiskAcknowledgedMessage.encode message
  | .activeRiskAcknowledgeRejectedMessage message => ActiveRiskAcknowledgeRejectedMessage.encode message
  | .activeRiskQuantityUpdateNotificationMessage message => ActiveRiskQuantityUpdateNotificationMessage.encode message
  | .cpVolumeThresholdStateMessage message => CpVolumeThresholdStateMessage.encode message
  | .cpExecutedNotionalThresholdStateMessage message => CpExecutedNotionalThresholdStateMessage.encode message
  | .cpTotalExecutionsThresholdStateMessage message => CpTotalExecutionsThresholdStateMessage.encode message
  | .cpPercentOutstandingContractsThresholdStateMessage message => CpPercentOutstandingContractsThresholdStateMessage.encode message
  | .cpBreachCountThresholdStateMessage message => CpBreachCountThresholdStateMessage.encode message
  | .manualCpBreachTriggerPendingMessage message => ManualCpBreachTriggerPendingMessage.encode message
  | .manualCpBreachTriggerDoneMessage message => ManualCpBreachTriggerDoneMessage.encode message
  | .riskThresholdUpdateRejectedMessage message => RiskThresholdUpdateRejectedMessage.encode message
  | .passiveRiskThresholdNotificationMessage message => PassiveRiskThresholdNotificationMessage.encode message
  | .singleOrderAllowIsoOrdersStateMessage message => SingleOrderAllowIsoOrdersStateMessage.encode message
  | .singleOrderAllowOrdersInCrossedMarketStateMessage message => SingleOrderAllowOrdersInCrossedMarketStateMessage.encode message
  | .singleOrderMaxNotionalThresholdStateMessage message => SingleOrderMaxNotionalThresholdStateMessage.encode message
  | .singleOrderMaxContractsThresholdStateMessage message => SingleOrderMaxContractsThresholdStateMessage.encode message
  | .singleOrderAllowMarketOrdersStateMessage message => SingleOrderAllowMarketOrdersStateMessage.encode message
  | .singleOrderRestrictedUnderlierStateMessage message => SingleOrderRestrictedUnderlierStateMessage.encode message
  | .riskSettingsQueryDoneMessage message => RiskSettingsQueryDoneMessage.encode message
  | .riskSettingsQueryRejectedMessage message => RiskSettingsQueryRejectedMessage.encode message
  | .manualCpBreachTriggerRejectedMessage message => ManualCpBreachTriggerRejectedMessage.encode message
  | .breachClearRejectedMessage message => BreachClearRejectedMessage.encode message
  | .breachClearedMessage message => BreachClearedMessage.encode message
  | .breachClearAllAcceptedMessage message => BreachClearAllAcceptedMessage.encode message
  | .breachClearAllRejectedMessage message => BreachClearAllRejectedMessage.encode message
  | .breachClearAllByEfidOrUnderlierAcceptedMessage message => BreachClearAllByEfidOrUnderlierAcceptedMessage.encode message
  | .breachClearAllByEfidOrUnderlierRejectedMessage message => BreachClearAllByEfidOrUnderlierRejectedMessage.encode message
  | .cpGrossNotionalThresholdStateMessage message => CpGrossNotionalThresholdStateMessage.encode message
  | .cpMarketOrderGrossNotionalThresholdStateMessage message => CpMarketOrderGrossNotionalThresholdStateMessage.encode message
  | .cpNetNotionalThresholdStateMessage message => CpNetNotionalThresholdStateMessage.encode message
  | .cpMarketOrderNetNotionalThresholdStateMessage message => CpMarketOrderNetNotionalThresholdStateMessage.encode message
  | .cpDuplicateOrderThresholdStateMessage message => CpDuplicateOrderThresholdStateMessage.encode message
  | .cpOrderRateThresholdStateMessage message => CpOrderRateThresholdStateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 67 := by
  cases message with
  | riskSettingsQueryMessage inner =>
    simp only [encode, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeRequestMessage inner =>
    simp only [encode, ActiveRiskThresholdChangeRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgementRequestMessage inner =>
    simp only [encode, ActiveRiskAcknowledgementRequestMessage.encode_length]
    omega
  | cpVolumeThresholdChangeRequestMessage inner =>
    simp only [encode, CpVolumeThresholdChangeRequestMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpExecutedNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeRequestMessage inner =>
    simp only [encode, CpTotalExecutionsThresholdChangeRequestMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeRequestMessage inner =>
    simp only [encode, CpPercentOutstandingContractsThresholdChangeRequestMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeRequestMessage inner =>
    simp only [encode, CpBreachCountThresholdChangeRequestMessage.encode_length]
    omega
  | manualCpBreachTriggerRequestMessage inner =>
    simp only [encode, ManualCpBreachTriggerRequestMessage.encode_length]
    omega
  | cpClearBreachRequestMessage inner =>
    simp only [encode, CpClearBreachRequestMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowIsoOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeRequestMessage inner =>
    simp only [encode, SingleOrderMaxNotionalChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeRequestMessage inner =>
    simp only [encode, SingleOrderMaxContractsChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowMarketOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierChangeRequestMessage inner =>
    simp only [encode, SingleOrderRestrictedUnderlierChangeRequestMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeRequestMessage inner =>
    simp only [encode, CpDuplicateOrderThresholdChangeRequestMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeRequestMessage inner =>
    simp only [encode, CpOrderRateThresholdChangeRequestMessage.encode_length]
    omega
  | cpClearAllBreachesRequestMessage inner =>
    simp only [encode, CpClearAllBreachesRequestMessage.encode_length]
    omega
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage inner =>
    simp only [encode, CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgeAllRequestMessage inner =>
    simp only [encode, ActiveRiskAcknowledgeAllRequestMessage.encode_length]
    omega
  | activeRiskThresholdStateMessage inner =>
    simp only [encode, ActiveRiskThresholdStateMessage.encode_length]
    omega
  | activeRiskThresholdChangeRejectedMessage inner =>
    simp only [encode, ActiveRiskThresholdChangeRejectedMessage.encode_length]
    omega
  | activeRiskAcknowledgedMessage inner =>
    simp only [encode, ActiveRiskAcknowledgedMessage.encode_length]
    omega
  | activeRiskAcknowledgeRejectedMessage inner =>
    simp only [encode, ActiveRiskAcknowledgeRejectedMessage.encode_length]
    omega
  | activeRiskQuantityUpdateNotificationMessage inner =>
    simp only [encode, ActiveRiskQuantityUpdateNotificationMessage.encode_length]
    omega
  | cpVolumeThresholdStateMessage inner =>
    simp only [encode, CpVolumeThresholdStateMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdStateMessage inner =>
    simp only [encode, CpExecutedNotionalThresholdStateMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdStateMessage inner =>
    simp only [encode, CpTotalExecutionsThresholdStateMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdStateMessage inner =>
    simp only [encode, CpPercentOutstandingContractsThresholdStateMessage.encode_length]
    omega
  | cpBreachCountThresholdStateMessage inner =>
    simp only [encode, CpBreachCountThresholdStateMessage.encode_length]
    omega
  | manualCpBreachTriggerPendingMessage inner =>
    simp only [encode, ManualCpBreachTriggerPendingMessage.encode_length]
    omega
  | manualCpBreachTriggerDoneMessage inner =>
    simp only [encode, ManualCpBreachTriggerDoneMessage.encode_length]
    omega
  | riskThresholdUpdateRejectedMessage inner =>
    simp only [encode, RiskThresholdUpdateRejectedMessage.encode_length]
    omega
  | passiveRiskThresholdNotificationMessage inner =>
    simp only [encode, PassiveRiskThresholdNotificationMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersStateMessage inner =>
    simp only [encode, SingleOrderAllowIsoOrdersStateMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketStateMessage inner =>
    simp only [encode, SingleOrderAllowOrdersInCrossedMarketStateMessage.encode_length]
    omega
  | singleOrderMaxNotionalThresholdStateMessage inner =>
    simp only [encode, SingleOrderMaxNotionalThresholdStateMessage.encode_length]
    omega
  | singleOrderMaxContractsThresholdStateMessage inner =>
    simp only [encode, SingleOrderMaxContractsThresholdStateMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersStateMessage inner =>
    simp only [encode, SingleOrderAllowMarketOrdersStateMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierStateMessage inner =>
    simp only [encode, SingleOrderRestrictedUnderlierStateMessage.encode_length]
    omega
  | riskSettingsQueryDoneMessage inner =>
    simp only [encode, RiskSettingsQueryDoneMessage.encode_length]
    omega
  | riskSettingsQueryRejectedMessage inner =>
    simp only [encode, RiskSettingsQueryRejectedMessage.encode_length]
    omega
  | manualCpBreachTriggerRejectedMessage inner =>
    simp only [encode, ManualCpBreachTriggerRejectedMessage.encode_length]
    omega
  | breachClearRejectedMessage inner =>
    simp only [encode, BreachClearRejectedMessage.encode_length]
    omega
  | breachClearedMessage inner =>
    simp only [encode, BreachClearedMessage.encode_length]
    omega
  | breachClearAllAcceptedMessage inner =>
    simp only [encode, BreachClearAllAcceptedMessage.encode_length]
    omega
  | breachClearAllRejectedMessage inner =>
    simp only [encode, BreachClearAllRejectedMessage.encode_length]
    omega
  | breachClearAllByEfidOrUnderlierAcceptedMessage inner =>
    simp only [encode, BreachClearAllByEfidOrUnderlierAcceptedMessage.encode_length]
    omega
  | breachClearAllByEfidOrUnderlierRejectedMessage inner =>
    simp only [encode, BreachClearAllByEfidOrUnderlierRejectedMessage.encode_length]
    omega
  | cpGrossNotionalThresholdStateMessage inner =>
    simp only [encode, CpGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdStateMessage inner =>
    simp only [encode, CpMarketOrderGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpNetNotionalThresholdStateMessage inner =>
    simp only [encode, CpNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdStateMessage inner =>
    simp only [encode, CpMarketOrderNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdStateMessage inner =>
    simp only [encode, CpDuplicateOrderThresholdStateMessage.encode_length]
    omega
  | cpOrderRateThresholdStateMessage inner =>
    simp only [encode, CpOrderRateThresholdStateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (RiskSettingsQueryMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryMessage message, rest)
  else if tag = 2 then (ActiveRiskThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdChangeRequestMessage message, rest)
  else if tag = 3 then (ActiveRiskAcknowledgementRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgementRequestMessage message, rest)
  else if tag = 4 then (CpVolumeThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpVolumeThresholdChangeRequestMessage message, rest)
  else if tag = 5 then (CpExecutedNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpExecutedNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 6 then (CpTotalExecutionsThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpTotalExecutionsThresholdChangeRequestMessage message, rest)
  else if tag = 7 then (CpPercentOutstandingContractsThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpPercentOutstandingContractsThresholdChangeRequestMessage message, rest)
  else if tag = 8 then (CpBreachCountThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpBreachCountThresholdChangeRequestMessage message, rest)
  else if tag = 9 then (ManualCpBreachTriggerRequestMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerRequestMessage message, rest)
  else if tag = 10 then (CpClearBreachRequestMessage.decode bytes).map fun (message, rest) => (.cpClearBreachRequestMessage message, rest)
  else if tag = 11 then (SingleOrderAllowIsoOrdersChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowIsoOrdersChangeRequestMessage message, rest)
  else if tag = 12 then (SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowOrdersInCrossedMarketChangeRequestMessage message, rest)
  else if tag = 13 then (SingleOrderMaxNotionalChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxNotionalChangeRequestMessage message, rest)
  else if tag = 14 then (SingleOrderMaxContractsChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxContractsChangeRequestMessage message, rest)
  else if tag = 15 then (SingleOrderAllowMarketOrdersChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowMarketOrdersChangeRequestMessage message, rest)
  else if tag = 16 then (SingleOrderRestrictedUnderlierChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderRestrictedUnderlierChangeRequestMessage message, rest)
  else if tag = 18 then (CpGrossNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpGrossNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 19 then (CpMarketOrderGrossNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderGrossNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 20 then (CpNetNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpNetNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 21 then (CpMarketOrderNetNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderNetNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 22 then (CpDuplicateOrderThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpDuplicateOrderThresholdChangeRequestMessage message, rest)
  else if tag = 23 then (CpOrderRateThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpOrderRateThresholdChangeRequestMessage message, rest)
  else if tag = 24 then (CpClearAllBreachesRequestMessage.decode bytes).map fun (message, rest) => (.cpClearAllBreachesRequestMessage message, rest)
  else if tag = 25 then (CpClearAllBreachesByEfidOrUnderlierRequestMessage.decode bytes).map fun (message, rest) => (.cpClearAllBreachesByEfidOrUnderlierRequestMessage message, rest)
  else if tag = 26 then (ActiveRiskAcknowledgeAllRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgeAllRequestMessage message, rest)
  else if tag = 30 then (ActiveRiskThresholdStateMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdStateMessage message, rest)
  else if tag = 31 then (ActiveRiskThresholdChangeRejectedMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdChangeRejectedMessage message, rest)
  else if tag = 32 then (ActiveRiskAcknowledgedMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgedMessage message, rest)
  else if tag = 33 then (ActiveRiskAcknowledgeRejectedMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgeRejectedMessage message, rest)
  else if tag = 34 then (ActiveRiskQuantityUpdateNotificationMessage.decode bytes).map fun (message, rest) => (.activeRiskQuantityUpdateNotificationMessage message, rest)
  else if tag = 35 then (CpVolumeThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpVolumeThresholdStateMessage message, rest)
  else if tag = 36 then (CpExecutedNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpExecutedNotionalThresholdStateMessage message, rest)
  else if tag = 37 then (CpTotalExecutionsThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpTotalExecutionsThresholdStateMessage message, rest)
  else if tag = 38 then (CpPercentOutstandingContractsThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpPercentOutstandingContractsThresholdStateMessage message, rest)
  else if tag = 39 then (CpBreachCountThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpBreachCountThresholdStateMessage message, rest)
  else if tag = 40 then (ManualCpBreachTriggerPendingMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerPendingMessage message, rest)
  else if tag = 41 then (ManualCpBreachTriggerDoneMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerDoneMessage message, rest)
  else if tag = 42 then (RiskThresholdUpdateRejectedMessage.decode bytes).map fun (message, rest) => (.riskThresholdUpdateRejectedMessage message, rest)
  else if tag = 43 then (PassiveRiskThresholdNotificationMessage.decode bytes).map fun (message, rest) => (.passiveRiskThresholdNotificationMessage message, rest)
  else if tag = 44 then (SingleOrderAllowIsoOrdersStateMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowIsoOrdersStateMessage message, rest)
  else if tag = 45 then (SingleOrderAllowOrdersInCrossedMarketStateMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowOrdersInCrossedMarketStateMessage message, rest)
  else if tag = 46 then (SingleOrderMaxNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxNotionalThresholdStateMessage message, rest)
  else if tag = 47 then (SingleOrderMaxContractsThresholdStateMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxContractsThresholdStateMessage message, rest)
  else if tag = 66 then (SingleOrderAllowMarketOrdersStateMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowMarketOrdersStateMessage message, rest)
  else if tag = 67 then (SingleOrderRestrictedUnderlierStateMessage.decode bytes).map fun (message, rest) => (.singleOrderRestrictedUnderlierStateMessage message, rest)
  else if tag = 48 then (RiskSettingsQueryDoneMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryDoneMessage message, rest)
  else if tag = 49 then (RiskSettingsQueryRejectedMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryRejectedMessage message, rest)
  else if tag = 50 then (ManualCpBreachTriggerRejectedMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerRejectedMessage message, rest)
  else if tag = 51 then (BreachClearRejectedMessage.decode bytes).map fun (message, rest) => (.breachClearRejectedMessage message, rest)
  else if tag = 52 then (BreachClearedMessage.decode bytes).map fun (message, rest) => (.breachClearedMessage message, rest)
  else if tag = 53 then (BreachClearAllAcceptedMessage.decode bytes).map fun (message, rest) => (.breachClearAllAcceptedMessage message, rest)
  else if tag = 69 then (BreachClearAllRejectedMessage.decode bytes).map fun (message, rest) => (.breachClearAllRejectedMessage message, rest)
  else if tag = 54 then (BreachClearAllByEfidOrUnderlierAcceptedMessage.decode bytes).map fun (message, rest) => (.breachClearAllByEfidOrUnderlierAcceptedMessage message, rest)
  else if tag = 68 then (BreachClearAllByEfidOrUnderlierRejectedMessage.decode bytes).map fun (message, rest) => (.breachClearAllByEfidOrUnderlierRejectedMessage message, rest)
  else if tag = 60 then (CpGrossNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpGrossNotionalThresholdStateMessage message, rest)
  else if tag = 61 then (CpMarketOrderGrossNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderGrossNotionalThresholdStateMessage message, rest)
  else if tag = 62 then (CpNetNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpNetNotionalThresholdStateMessage message, rest)
  else if tag = 63 then (CpMarketOrderNetNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderNetNotionalThresholdStateMessage message, rest)
  else if tag = 64 then (CpDuplicateOrderThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpDuplicateOrderThresholdStateMessage message, rest)
  else if tag = 65 then (CpOrderRateThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpOrderRateThresholdStateMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 73 := by
  unfold encode
  cases message.payload with
  | riskSettingsQueryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgementRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgementRequestMessage.encode_length]
    omega
  | cpVolumeThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdChangeRequestMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdChangeRequestMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdChangeRequestMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdChangeRequestMessage.encode_length]
    omega
  | manualCpBreachTriggerRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerRequestMessage.encode_length]
    omega
  | cpClearBreachRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearBreachRequestMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowMarketOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderRestrictedUnderlierChangeRequestMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdChangeRequestMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdChangeRequestMessage.encode_length]
    omega
  | cpClearAllBreachesRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearAllBreachesRequestMessage.encode_length]
    omega
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgeAllRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgeAllRequestMessage.encode_length]
    omega
  | activeRiskThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdStateMessage.encode_length]
    omega
  | activeRiskThresholdChangeRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeRejectedMessage.encode_length]
    omega
  | activeRiskAcknowledgedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgedMessage.encode_length]
    omega
  | activeRiskAcknowledgeRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgeRejectedMessage.encode_length]
    omega
  | activeRiskQuantityUpdateNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskQuantityUpdateNotificationMessage.encode_length]
    omega
  | cpVolumeThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdStateMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdStateMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdStateMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdStateMessage.encode_length]
    omega
  | cpBreachCountThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdStateMessage.encode_length]
    omega
  | manualCpBreachTriggerPendingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerPendingMessage.encode_length]
    omega
  | manualCpBreachTriggerDoneMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerDoneMessage.encode_length]
    omega
  | riskThresholdUpdateRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskThresholdUpdateRejectedMessage.encode_length]
    omega
  | passiveRiskThresholdNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PassiveRiskThresholdNotificationMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersStateMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketStateMessage.encode_length]
    omega
  | singleOrderMaxNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalThresholdStateMessage.encode_length]
    omega
  | singleOrderMaxContractsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsThresholdStateMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowMarketOrdersStateMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderRestrictedUnderlierStateMessage.encode_length]
    omega
  | riskSettingsQueryDoneMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryDoneMessage.encode_length]
    omega
  | riskSettingsQueryRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryRejectedMessage.encode_length]
    omega
  | manualCpBreachTriggerRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerRejectedMessage.encode_length]
    omega
  | breachClearRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearRejectedMessage.encode_length]
    omega
  | breachClearedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearedMessage.encode_length]
    omega
  | breachClearAllAcceptedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearAllAcceptedMessage.encode_length]
    omega
  | breachClearAllRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearAllRejectedMessage.encode_length]
    omega
  | breachClearAllByEfidOrUnderlierAcceptedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearAllByEfidOrUnderlierAcceptedMessage.encode_length]
    omega
  | breachClearAllByEfidOrUnderlierRejectedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearAllByEfidOrUnderlierRejectedMessage.encode_length]
    omega
  | cpGrossNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpNetNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdStateMessage.encode_length]
    omega
  | cpOrderRateThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdStateMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end UnsequencedMessage

/-- Any Client Data, selected by Message Type -/
inductive ClientData where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  deriving DecidableEq, Repr

namespace ClientData

/-- The Message Type each message is sent under -/
def tag : ClientData → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104

def encode : ClientData → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientData × List UInt8) :=
  if tag = 100 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 101 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).map fun (message, rest) => (.replayAllRequestMessage message, rest)
  else if tag = 103 then (StreamRequestMessage.decode bytes).map fun (message, rest) => (.streamRequestMessage message, rest)
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun (message, rest) => (.unsequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientData

/-- Client Packet -/
structure ClientPacket where
  messageLength : BitVec 16
  clientData : ClientData
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientData.tag message.clientData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientData.encode message.clientData))

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientData, bytes) ← ClientData.decode messageType bytes
  pure ({ messageLength, clientData }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientData.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.MemxMemxoptionsRiskcontrolSbeV17Client
