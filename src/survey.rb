#! /usr/bin/ruby -w
# -*- coding: utf-8 -*-

 ###############################################
#                                               #
#  Reports how many times each Texinfo command  #
#  is used in the file given as an argument.    #
#                                               #
#  Copyleft Andres Raba 2013, GNU GPL v.3.      #
#                                               #
 ###############################################

if (ARGV[0])
  texi_file = File.open(ARGV[0], "r")
  texi = texi_file.read
  texi_file.close
else
  puts "First argument should be Texinfo file.\n"
  exit
end

pattern = %r/
    (?:
       @([^\w ])           |  # 1. non-alphabetic command, like @*
       @(\w+)\{\}          |  # 2. aphabetic command (ac) without arguments, like @dots{}
       @(\w+)\{            |  # 3. ac that requires arguments, like @acronym{GCD}
       ^@(?!end)(\w+)\s+   |  # 4. ac that takes an entire line, like @chapter
       ^@end\s+(\w+))         # 5. ac that creates an environment (e.g. @tex .. @end tex)
    /mx

texi_tags = [{}, {}, {}, {}, {}, {}]

# This template is borrowed from Pickaxe 1.9, page 101.
class PatternFinder
  include Enumerable
  def initialize(string)
    @string = string
  end
  def each (pattern)
    @string.scan(pattern) do |match|
      yield match
    end
  end
end

tagsearcher = PatternFinder.new(texi) 

tagsearcher.each(pattern) do |result|
  result.each_with_index do |val, idx|
    type = idx + 1
    if val
      if texi_tags[type][val]
        texi_tags[type][val] += 1
      else
        texi_tags[type][val] = 1
      end
    end
  end
end

# Delete the type 4 keywords that already are in type 5
texi_tags[5].keys.each do |key|
  texi_tags[4].delete(key)
end

desc = {
  1 => 'non-alphabetic command, like @*',
  2 => 'aphabetic command (ac) without arguments, like @dots{}',
  3 => 'ac that requires arguments, like @acronym{GCD}',
  4 => 'ac that takes an entire line, like @chapter',
  5 => 'ac that creates an environment (e.g. @tex .. @end tex)'
}

print "\n"

# Print report
(1..5).to_a.each do |type|
  title = "Type #{type}: #{desc[type]}\n"
  print title
  print "=" * title.length, "\n"
  texi_tags[type].keys.sort.each do |tag|
    print tag
    print "(", texi_tags[type][tag], ")"
    print " "
  end
  print "\n\n"
end
