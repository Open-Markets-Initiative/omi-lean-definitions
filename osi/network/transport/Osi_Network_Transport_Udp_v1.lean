import Wire

/-!
# Open Systems Interconnection Transport v1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OsiNetworkTransportUdpV1

/-- Udp Datagram -/
structure UdpDatagram where
  udpSourcePort : BitVec 16
  udpDestinationPort : BitVec 16
  udpChecksum : BitVec 16
  udpPayload : Capped 65527
  deriving DecidableEq, Repr

namespace UdpDatagram

def encodeBody (message : UdpDatagram) : List UInt8 :=
  encodeUInt 2 message.udpChecksum
    ++ (message.udpPayload.val)

def decodeBody (udpSourcePort : BitVec 16) (udpDestinationPort : BitVec 16) (bytes : List UInt8) : Option UdpDatagram := do
  let (udpChecksum, bytes) ← decodeUInt 2 bytes
  let udpPayload_ := bytes
  if fits_udpPayload : udpPayload_.length ≤ 65527 then
    pure { udpSourcePort, udpDestinationPort, udpChecksum, udpPayload := ⟨udpPayload_, fits_udpPayload⟩ }
  else none

theorem decodeBody_encodeBody (message : UdpDatagram) : decodeBody message.udpSourcePort message.udpDestinationPort (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.udpPayload.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : UdpDatagram) : (encodeBody message).length + 6 < 256 ^ 2 := by
  have bound_udpPayload := message.udpPayload.length_le
  unfold encodeBody
  simp only [List.length_append, encodeUInt_length]
  omega

/-- Size rule: Udp Length counts the bytes after it plus 6, so it is written from the body and checked on decode; Udp Source Port, Udp Destination Port are read ahead of it -/
def encode (message : UdpDatagram) : List UInt8 :=
  encodeUInt 2 message.udpSourcePort
    ++ (encodeUInt 2 message.udpDestinationPort
    ++ (encodeFramed 2 6 encodeBody message))

def decode (bytes : List UInt8) : Option (UdpDatagram × List UInt8) := do
  let (udpSourcePort, bytes) ← decodeUInt 2 bytes
  let (udpDestinationPort, bytes) ← decodeUInt 2 bytes
  decodeFramedAll 2 6 (decodeBody udpSourcePort udpDestinationPort) bytes

@[simp] theorem decode_encode (message : UdpDatagram) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramedAll_encodeFramed 2 6 encodeBody (decodeBody message.udpSourcePort message.udpDestinationPort) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : UdpDatagram) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

end UdpDatagram

end Omi.OsiNetworkTransportUdpV1
