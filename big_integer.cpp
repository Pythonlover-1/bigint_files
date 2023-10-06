#include "big_integer.h"

#include <charconv>
#include <cmath>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <ostream>
#include <stdexcept>
#include <tuple>
#include <vector>


big_integer::big_integer() = default;

big_integer::big_integer(const big_integer& other) = default;

big_integer::big_integer(int a) {
  numeric_constructor(a);
}

big_integer::big_integer(long a) {
  numeric_constructor(a);
}

big_integer::big_integer(long long a) {
  numeric_constructor(a);
}

big_integer::big_integer(unsigned a) {
  numeric_constructor(a);
}

big_integer::big_integer(unsigned long a) {
  numeric_constructor(a);
}

big_integer::big_integer(unsigned long long a) {
  numeric_constructor(a);
}

big_integer::big_integer(const std::string& str) {
  std::size_t end_pos = 0;
  uint32_t current_digit;
  std::size_t ind = str.starts_with('-') ? 1 : 0;
  do {
    end_pos = std::min(ind + 9, str.size());
    auto [ptr, ec] = std::from_chars(str.data() + ind, str.data() + end_pos, current_digit);
    if (ptr != str.data() + end_pos || ec != std::errc()) {
      throw std::invalid_argument("Not a number");
    }
    mul_big_small(str.length() - ind < 9 ? std::pow(10, str.length() - ind) : taked_digits);
    add_big_small(current_digit);
    ind += 9;
  } while (ind < str.length());
  clean_zeros();
  if (!digits_.empty() && str.starts_with('-')) {
    is_neg = true;
  }
}

big_integer::~big_integer() = default;

big_integer& big_integer::operator=(const big_integer& other) {
  if (&other != this) {
    big_integer(other).swap(*this);
  }
  return *this;
}

big_integer& big_integer::operator+=(const big_integer& rhs) {
  if (rhs.is_neg == is_neg) {
    uint64_t carry = 0;
    std::size_t index = 0;
    add_zeros(*this, std::max(rhs.digits_.size(), digits_.size()) + 1);
    for (; index < rhs.digits_.size(); index++) {
      carry += (static_cast<uint64_t>(rhs.digits_[index]) + digits_[index]);
      digits_[index] = carry % base;
      carry /= base;
    }
    for (; index < digits_.size() - 1 && carry != 0; index++) {
      carry += digits_[index];
      digits_[index] = carry % base;
      carry /= base;
    }
    digits_[digits_.size() - 1] = carry;
    clean_zeros();
  } else {
    is_neg = rhs.is_neg;
    *this -= rhs;
    is_neg = !is_neg;
  }
  clean_zeros();
  if (digits_.empty()) {
    is_neg = false;
  }
  return *this;
}

big_integer& big_integer::operator-=(const big_integer& rhs) {
  if (is_neg != rhs.is_neg) {
    is_neg = rhs.is_neg;
    *this += rhs;
    is_neg = !is_neg;
  } else {
    bool is_more = *this >= rhs;
    if (!(is_more ^ is_neg)) {
      is_neg = !rhs.is_neg;
      sub_by_modules(rhs, *this);
    } else {
      sub_by_modules(*this, rhs);
    }
  }
  return *this;
}

big_integer& big_integer::operator*=(const big_integer& rhs) {
  uint64_t current_digit;
  std::size_t old_size = digits_.size();
  digits_.resize(digits_.size() + rhs.digits_.size(), 0);
  uint64_t carry = 0;
  for (std::size_t shifted_index_this = old_size; shifted_index_this > 0; shifted_index_this--) {
    std::size_t index_this = shifted_index_this - 1;
    current_digit = digits_[index_this];
    digits_[index_this] = 0;
    for (std::size_t index_rhs = 0; index_rhs < rhs.digits_.size(); index_rhs++) {
      carry += digits_[index_this + index_rhs];
      carry += current_digit * rhs.digits_[index_rhs];
      digits_[index_this + index_rhs] = carry % base;
      carry /= base;
    }
    std::size_t pos = rhs.digits_.size();
    while (carry > 0) {
      carry += digits_[index_this + pos];
      digits_[index_this + pos] = carry % base;
      carry /= base;
      pos++;
    }
  }
  clean_zeros();
  if (is_neg == rhs.is_neg || digits_.empty()) {
    is_neg = false;
  } else {
    is_neg = true;
  }
  return *this;
}

big_integer& big_integer::operator/=(const big_integer& rhs) {
  *this = longdivide(*this, rhs).first;
  clean_zeros();
  if (digits_.empty()) {
    is_neg = false;
  }
  return *this;
}

big_integer& big_integer::operator%=(const big_integer& rhs) {
  *this = longdivide(*this, rhs).second;
  clean_zeros();
  if (digits_.empty()) {
    is_neg = false;
  }
  return *this;
}

big_integer& big_integer::operator&=(const big_integer& rhs) {
  uint32_t leading_numbers = rhs.is_neg ? std::numeric_limits<uint32_t>::max() : 0;
  uint32_t this_carry = 1;
  uint32_t borrow = 1;
  uint32_t rhs_carry = 1;
  uint32_t this_digit;
  uint32_t rhs_digit;
  bool result_neg = (is_neg & rhs.is_neg);
  add_zeros(*this, rhs.digits_.size());
  for (std::size_t index = 0; index < digits_.size(); index++) {
    std::tie(this_digit, this_carry) = return_digit(digits_[index], this_carry, is_neg);
    if (index >= rhs.digits_.size()) {
      rhs_digit = leading_numbers;
    } else {
      std::tie(rhs_digit, rhs_carry) = return_digit(rhs.digits_[index], rhs_carry, rhs.is_neg);
    }
    std::tie(digits_[index], borrow) = transform_back(this_digit & rhs_digit, borrow, result_neg);
  }
  is_neg = result_neg;
  clean_zeros();
  return *this;
}

big_integer& big_integer::operator|=(const big_integer& rhs) {
  uint32_t leading_numbers = rhs.is_neg ? std::numeric_limits<uint32_t>::max() : 0;
  uint32_t this_carry = 1;
  uint32_t borrow = 1;
  uint32_t rhs_carry = 1;
  uint32_t this_digit;
  uint32_t rhs_digit;
  bool result_neg = (is_neg || rhs.is_neg);
  add_zeros(*this, rhs.digits_.size());
  for (std::size_t index = 0; index < digits_.size(); index++) {
    std::tie(this_digit, this_carry) = return_digit(digits_[index], this_carry, is_neg);
    if (index >= rhs.digits_.size()) {
      rhs_digit = leading_numbers;
    } else {
      std::tie(rhs_digit, rhs_carry) = return_digit(rhs.digits_[index], rhs_carry, rhs.is_neg);
    }
    std::tie(digits_[index], borrow) = transform_back(this_digit | rhs_digit, borrow, result_neg);
  }
  is_neg = result_neg;
  clean_zeros();
  return *this;
}

big_integer& big_integer::operator^=(const big_integer& rhs) {
  uint32_t leading_numbers = rhs.is_neg ? std::numeric_limits<uint32_t>::max() : 0;
  uint32_t this_carry = 1;
  uint32_t borrow = 1;
  uint32_t rhs_carry = 1;
  uint32_t this_digit;
  uint32_t rhs_digit;
  bool result_neg = (is_neg != rhs.is_neg);
  add_zeros(*this, rhs.digits_.size());
  for (std::size_t index = 0; index < digits_.size(); index++) {
    std::tie(this_digit, this_carry) = return_digit(digits_[index], this_carry, is_neg);
    if (index >= rhs.digits_.size()) {
      rhs_digit = leading_numbers;
    } else {
      std::tie(rhs_digit, rhs_carry) = return_digit(rhs.digits_[index], rhs_carry, rhs.is_neg);
    }
    std::tie(digits_[index], borrow) = transform_back(this_digit ^ rhs_digit, borrow, result_neg);
  }
  is_neg = result_neg;
  clean_zeros();
  return *this;
}

big_integer& big_integer::operator<<=(int rhs) {
  if (digits_.empty()) {
    return *this;
  }
  uint32_t leading_numbers = is_neg ? std::numeric_limits<uint32_t>::max() : 0;
  uint32_t div = rhs / 32;
  uint32_t mod = rhs % 32;
  uint32_t borrow, cur_carry, shifted_carry, shifted_digit, cur_digit;
  std::size_t carry_index = 0;
  std::size_t old_size = digits_.size();
  for (; carry_index < digits_.size(); carry_index++) {
    if (digits_[carry_index]) {
      break;
    }
  }
  digits_.resize(digits_.size() + (rhs + 31) / 32, 0);
  for (std::size_t shifted_index = old_size + div + 1; shifted_index > 0; shifted_index--) {
    std::size_t index = shifted_index - 1;
    if (div > index) {
      cur_digit = 0;
    } else if (index - div == old_size) {
      cur_digit = leading_numbers;
    } else {
      std::tie(cur_digit, cur_carry) = return_digit(digits_[index - div], (index - div) <= carry_index, is_neg);
    }
    cur_digit <<= mod;
    if (div + 1 <= index && mod > 0) {
      std::tie(shifted_digit, shifted_carry) =
          return_digit(digits_[index - (div + 1)], (index - (div + 1)) <= carry_index, is_neg);
      cur_digit += (shifted_digit >> (32 - mod));
    }
    std::tie(digits_[index], borrow) = transform_back(cur_digit, index <= carry_index + div, is_neg);
  }
  clean_zeros();
  return *this;
}

big_integer& big_integer::operator>>=(int rhs) {
  uint32_t leading_numbers = is_neg ? std::numeric_limits<uint32_t>::max() : 0;
  uint32_t div = rhs / 32;
  uint32_t mod = rhs % 32;
  uint32_t borrow = 1;
  uint32_t cur_carry = 1;
  uint32_t shifted_carry = 1;
  uint32_t cur_digit = 0;
  uint32_t shifted_digit = 0;
  std::tie(shifted_digit, shifted_carry) = return_digit(digits_[0], shifted_carry, is_neg);
  for (std::size_t i = 0; i < div && i < digits_.size(); i++) {
    std::tie(cur_digit, cur_carry) = return_digit(digits_[i], cur_carry, is_neg);
    if (i + 1 < digits_.size()) {
      std::tie(shifted_digit, shifted_carry) = return_digit(digits_[i + 1], shifted_carry, is_neg);
    }
  }
  for (std::size_t index = 0; index < digits_.size(); index++) {
    if (index + div >= digits_.size()) {
      cur_digit = leading_numbers;
    } else {
      std::tie(cur_digit, cur_carry) = return_digit(digits_[index + div], cur_carry, is_neg);
    }
    cur_digit >>= mod;
    if (index + div + 1 < digits_.size()) {
      std::tie(shifted_digit, shifted_carry) = return_digit(digits_[index + (div + 1)], shifted_carry, is_neg);
    } else {
      shifted_digit = leading_numbers;
    }
    if (mod > 0) {
      cur_digit += (shifted_digit << (32 - mod));
    }
    std::tie(digits_[index], borrow) = transform_back(cur_digit, borrow, is_neg);
  }
  clean_zeros();
  return *this;
}

big_integer big_integer::operator+() const {
  return *this;
}

big_integer big_integer::operator-() const {
  big_integer tmp = big_integer(*this);
  if (!tmp.digits_.empty()) {
    tmp.is_neg = not is_neg;
  }
  return tmp;
}

big_integer big_integer::operator~() const {
  big_integer tmp = big_integer(*this);
  tmp.is_neg = not is_neg;
  uint32_t borrow = 1;
  uint32_t this_carry = 1;
  uint32_t this_digit = 0;
  for (std::size_t index = 0; index < tmp.digits_.size(); index++) {
    std::tie(this_digit, this_carry) = return_digit(digits_[index], this_carry, is_neg);
    std::tie(tmp.digits_[index], borrow) = transform_back(~this_digit, borrow, tmp.is_neg);
  }
  tmp.clean_zeros();
  if (tmp.digits_.empty() && tmp.is_neg) {
    tmp.digits_.push_back(1);
  }
  return tmp;
}

big_integer& big_integer::operator++() {
  add_big_small(1);
  return *this;
}

big_integer big_integer::operator++(int) {
  big_integer tmp = *this;
  ++*this;
  return tmp;
}

big_integer& big_integer::operator--() {
  sub_big_small(1);
  return *this;
}

big_integer big_integer::operator--(int) {
  big_integer tmp = *this;
  --*this;
  return tmp;
}
#include <iostream>
std::pair<big_integer, big_integer> longdivide(big_integer& dividend, const big_integer& rhs) {
  if (rhs.digits_.size() > dividend.digits_.size()) {
    return std::make_pair(big_integer(0), dividend);
  } else if (rhs.digits_.size() == 1) {
    big_integer reminder = dividend.div_big_small(rhs.digits_[0]);
    reminder.is_neg = dividend.is_neg;
    dividend.is_neg = dividend.is_neg ^ rhs.is_neg;
    return std::make_pair(dividend, reminder);
  }
  bool dividend_old = dividend.is_neg;
  dividend.is_neg = false;
  big_integer divisor = rhs;
  bool divisor_old = divisor.is_neg;
  divisor.is_neg = false;
  uint32_t normalize_mult = 0;
  if (rhs.digits_.back() < (1 << 31)) {
    normalize_mult = divisor.normalize();
    dividend.mul_big_small(normalize_mult);
  }
  uint32_t q_j, j;
  std::size_t n = divisor.digits_.size();
  std::size_t m = dividend.digits_.size() - divisor.digits_.size();
  divisor.digits_.insert(divisor.digits_.begin(), m, 0);
  big_integer result;
  result.digits_.resize(m + 1);
  if (dividend >= divisor) {
    q_j = 1;
    dividend -= divisor;
  } else {
    q_j = 0;
  }
  result.digits_[m] = q_j;
  divisor >>= 32;
  for (std::size_t iter = m; iter > 0 && dividend.digits_.size() > 1; iter--) {
    j = iter - 1;
    q_j = std::min((dividend.digits_[n + j] * big_integer::base + dividend.digits_[n + j - 1]) / divisor.digits_.back(),
                   static_cast<uint64_t>(big_integer::base - 1));
    divisor.mul_big_small(q_j);
    dividend -= divisor;
    divisor.div_big_small(q_j);
    while (dividend.is_neg) {
      q_j--;
      dividend += divisor;
    }
    result.digits_[j] = q_j;
    divisor >>= 32;
  }
  if (normalize_mult > 0) {
    dividend.div_big_small(normalize_mult);
  }
  dividend.is_neg = dividend_old;
  result.is_neg = dividend_old ^ divisor_old;
  return std::make_pair(result, dividend);
}

big_integer operator+(const big_integer& a, const big_integer& b) {
  return big_integer(a) += b;
}

big_integer operator-(const big_integer& a, const big_integer& b) {
  return big_integer(a) -= b;
}

big_integer operator*(const big_integer& a, const big_integer& b) {
  return big_integer(a) *= b;
}

big_integer operator/(const big_integer& a, const big_integer& b) {
  return big_integer(a) /= b;
}

big_integer operator%(const big_integer& a, const big_integer& b) {
  return big_integer(a) %= b;
}

big_integer operator&(const big_integer& a, const big_integer& b) {
  return big_integer(a) &= b;
}

big_integer operator|(const big_integer& a, const big_integer& b) {
  return big_integer(a) |= b;
}

big_integer operator^(const big_integer& a, const big_integer& b) {
  return big_integer(a) ^= b;
}

big_integer operator<<(const big_integer& a, int b) {
  return big_integer(a) <<= b;
}

big_integer operator>>(const big_integer& a, int b) {
  return big_integer(a) >>= b;
}

bool operator==(const big_integer& a, const big_integer& b) {
  if (a.is_neg != b.is_neg) {
    return false;
  }
  if (a.digits_.size() == b.digits_.size()) {
    for (std::size_t ind = 0; ind < a.digits_.size(); ind++) {
      if (a.digits_[ind] != b.digits_[ind]) {
        return false;
      }
    }
    return true;
  } else if (a.digits_.empty() || b.digits_.empty()) {
    return a.digits_.empty() && b.digits_.empty();
  }
  return false;
}

bool operator!=(const big_integer& a, const big_integer& b) {
  return !(a == b);
}

bool operator<(const big_integer& a, const big_integer& b) {
  if (a.is_neg && not b.is_neg) {
    return true;
  }
  if (b.is_neg && not a.is_neg) {
    return false;
  }
  if (b.digits_.empty()) {
    return a.is_neg;
  }
  if (a.digits_.empty()) {
    return !(b.is_neg || b.digits_.empty());
  }
  if (a.digits_.size() != b.digits_.size()) {
    return (a.is_neg ? a.digits_.size() > b.digits_.size() : a.digits_.size() < b.digits_.size());
  }
  for (std::reverse_iterator index_a = a.digits_.rbegin(), index_b = b.digits_.rbegin(); index_a < a.digits_.rend();
       index_a++, index_b++) {
    if (*index_a != *index_b) {
      return (a.is_neg ? *index_a > *index_b : *index_a < *index_b);
    }
  }
  return false;
}

bool operator>(const big_integer& a, const big_integer& b) {
  return b < a;
}

bool operator<=(const big_integer& a, const big_integer& b) {
  return !(a > b);
}

bool operator>=(const big_integer& a, const big_integer& b) {
  return !(a < b);
}

std::string to_string(const big_integer& a) {
  std::string cur_number;
  std::string str = "";
  big_integer tmp = big_integer(a);
  if (tmp.digits_.empty()) {
    str = "0";
  }
  while (!tmp.digits_.empty()) {
    cur_number = std::to_string(tmp.div_big_small(big_integer::taked_digits));
    if (!tmp.digits_.empty()) {
      str = std::string(9 - cur_number.length(), '0').append(cur_number).append(str);
    } else {
      str = cur_number.append(str);
    }
  }
  if (a.is_neg) {
    str.insert(str.begin(), '-');
  }
  return str;
}

std::ostream& operator<<(std::ostream& out, const big_integer& a) {
  return out << to_string(a);
}