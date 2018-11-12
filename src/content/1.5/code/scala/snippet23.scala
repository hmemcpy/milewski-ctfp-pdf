sealed trait Contact
final case class PhoneNum(num: Int) extends Contact
final case class EmailAddr(addr: String) extends Contact