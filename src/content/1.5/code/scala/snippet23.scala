sealed trait Contact
case class PhoneNum(num: Int) extends Contact
case class EmailAddr(addr: String) extends Contact