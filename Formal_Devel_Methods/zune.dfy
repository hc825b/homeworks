method zune(d: int) returns (year: int)
{
  var b;
  var days := d;
  year := 0;
  while (days > 365)
    decreases days;
{
    b := IsLeapYear(year);
    
    if (b)
    {
        if (days > 366)
        {
            days := days - 366;
            year := year + 1;
        }
    }
    else
    {
        days := days - 365;
        year := year + 1;
    }
}
}

method IsLeapYear(years: int) returns (res: bool)

