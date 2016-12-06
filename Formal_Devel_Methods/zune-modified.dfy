method zune(d: int) returns (year: int)
{
  var b;
  var days := d;
  year := 0;
  while (days > 366)
    decreases days;
  {
    b := IsLeapYear(year);
    
    if (b)
    {
        days := days - 366;        
    }
    else
    {
        days := days - 365;
    }
    year := year + 1;
  }
  if(days > 365)
  {
    b := IsLeapYear(year);
    if(b)
    {
      year := year + 1;
      days := days - 365;
    }
  }
}

method IsLeapYear(years: int) returns (res: bool)