#!/usr/bin/env perl

 ######################################################
#                                                      #
#  Texinfo to LaTeX conversion script tailored to      #
#  handle the sicp.texi source. Does not work with     #
#  other Texinfo files, needs to be extended for       #
#  general utility.                                    #
#                                                      #
#  Copyleft 2013, 2015 Andres Raba,                    #
#  GNU General Public License, version 3.              #
#                                                      #
#  Disclaimer: No warranty. Author is not responsible  #
#  for accidental or deliberate data loss.             #
#  Please make backups before using this software.     #
#  See LICENSE for detailed terms.                     #
#                                                      #
 ######################################################

use 5.012;
use warnings;
use autodie;
use Getopt::Std;


# Sentinel to trigger Latex mode in code listings:
my $textrigger = '~'; 

# Latex preamble containing declarations 
# and ending with \begin{document}
my $preamble = swallow('preamble.tex');

# Postamble containing \end{document} etc.
my $postamble = swallow('postamble.tex');

# Hashmap for variables assigned with @set
my %values = ();


# Regular expressions for parsing Texinfo source
# ===============================================
# Match tag like @var or @*. Or match $ or %.
my $texi_tag = 
  qr/
      (?<tag>         # start of named capture
        \@            #   literal @-sign
        (?:           #   followed by one of:
          \w+         #     at least one word character
          |           #     ... or ...
          \W          #     one non-word-char
        )             #   end of non-capturing group
        |             #   ... or ...
        [\$%]         #   dollar or percent sign
      )               # end of named capture
  /x;

# Zero width match.
my $void = qr/^/;

# Swallow space.
my $space = qr/^[ \t]+/;

# Swallow space and newline.
my $empty = qr/^\s*\n/;

# Consume everything until end of line.
my $line = qr/^[ \t]*(?<arg>.*?)[ \t]*$/m;

# Match nested braces. Adapted from 'perldoc perl5100delta'.
my $braces = 
  qr/
      ^               # beginning of string
      (               # start of capture buffer 1  <--------.
        \{            #   opening brace                     |
          (?<arg>     #     start of named capture          |
            (?:       #       match one of:                 |
              [^{}]+  #         one or more non-braces      |
              |       #         ... or ...                  |
              (?1)    #         the whole structure again --'
            )*        #       zero or more times
          )           #     end of named capture
        \}            #   closing brace
      )               # end of capture buffer 1
  /mx;

# Match everything until '@end <tag>'
my $end = 
  sub { 
    my $tag = shift; 
    qr/
       ^              # beginning of string
       (?<arg>        # start of named capture
         .*?          #   anything zero or more times
       )              # end of named capture
       \@end\s+$tag   # '@end', some space, and given <tag>  
    /xms;
  };
    
# Functions for generating LaTeX markup fragments
# ================================================
sub bounce { # just bounce back the given string
  my $str = shift;
  return sub {
    return $str;
  }
}

sub setvalue { # write value to %values
  return sub {
    my $arg = shift;
    my ($variable, $value) = $arg =~ /(\w+)[ \t]+(\w.*)/;
    if ($variable and $value) {
      $values{$variable} = $value;
    } else {
      print "Warning: incomplete '\@set' command. ";
      print "Expected: '\@set <variable> <value>'.\n";
    }
    return '';
  }
}

sub value { # retrieve value from %values
  return sub {
    my $variable = shift;
    return $values{$variable};
  }
}

sub caption { # just expose the argument inside @caption{}
  return sub {
    my $arg = shift;
    return transform($arg, "caption");
  }
}

sub glue { # glue the tag on embraced arg
  my $tag = shift;
  my $unit = (shift or ''); # mainly to handle @sp
  return sub {
    my $arg = shift;
    my $env = (shift or '');
    my $color = '';
    if ($tag eq 'var' and $env eq 'scheme') {
      $color = "\\dark "; # an alias defined in the preamble
    }
    my $inner = transform($arg, $tag);
    my $linktype = ''; # prefix numerical links with 'Section':
    if ($tag eq 'link' and $inner =~ m/^\d/) {
      $linktype = 'Section ';
    }
    my $phantom = ''; # fix labels inside figure environment:
    if (($env eq 'figure' or $env eq 'heading') and $tag eq 'label') {
      $phantom = '\\phantomsection';
    }
    return "$phantom\\$tag\{$color$linktype$inner$unit\}";
  }
}

sub unnumbered { # chapters and sections without a number
  my $tag = shift;
  return sub {
    my $arg = shift;
    my $heading = glue($tag)->($arg);
    my $sectype = $tag; # section type (chapter, section, etc.)
    $sectype =~ s/\*//; # remove asterisk
    my $inner = transform($arg);
    return "$heading\n\\addcontentsline\{toc\}\{$sectype\}\{$inner\}";
  }
}

sub enclose { # enclose the arg in 'begin .. end' environment
  my $tag = shift;
  my $option = (shift or '');
  return sub {
    my $arg = shift;
    my $env = (shift or '');
    my $inner = transform($arg, $tag);
    my $prefix = '';
    if ($env eq 'footnote' and $tag eq 'scheme') {
      $prefix = 'small';
    }
    return "\\begin\{$prefix$tag\}$option$inner\\end\{$prefix$tag\}";
  }
}

sub inlinemath { # 
  return sub {
    my $arg = shift;
    my $env = (shift or '');
    my $color = '';
    if ($env eq 'scheme') {
      $color = "\\dark "; # an alias defined in the preamble
    }
    return "\\( $color$arg \\)";
  }
}

sub displaymath { # 
  return sub {
    my $arg = shift;
    return $arg;
  }
}

sub url { #
  return sub {
    my $arg = shift;
    my $inner = transform($arg, 'url');
    my ($link, $name) = split(/\s*,\s*/, $inner);
    if (!defined($name)) { $name = $link; }
    return "\\href\{$link\}\{$name\}";
  }
}

sub node { # extract first part of arg and make label out of it
  return sub {
    my $arg = shift;
    my $label = (split /,/, $arg)[0];
    $label =~ s/^(\d)/Section $1/; # prefix 'Section' to starting number
    return "\\label\{$label\}";
  }
}

sub itemize { # 
  return sub {
    my $arg = shift;
    my $inner = transform($arg, 'itemize');
    $inner =~ m/^(?<label>.*?)\n(?<items>.*$)/ms;
    my ($label, $items) = ($+{label}, $+{items});
    $label =~ s/\s//g; # delete whitespace
    if ($label and $label ne '\\bullet') {
      $items =~ s/\\item/\\item\[$label\]/g;
    }
    return "\\begin\{itemize\}\n$items\\end\{itemize\}";
  }
}

sub enumerate { # 
  return sub {
    my $arg = shift;
    my $inner = transform($arg, 'enumerate');
    $inner =~ m/^(?<label>.*?)\n(?<items>.*$)/ms;
    my ($label, $items) = ($+{label}, $+{items});
    $label =~ s/^\s*(.*)\s*$/$1/g; # delete peripheral whitespace
    if ($label and $label ne '1') {
      $label = '[' . $label . ']';
    } else {
      $label = '';
    }
    return "\\begin\{enumerate\}$label\n$items\\end\{enumerate\}";
  }
}

sub figure { # scrape the arg for figure components
  return sub {
    my $arg = shift;
    my $where = 'tb'; # default placement options (top or bottom)
    if ($arg =~ m/^\[([^]]+?)\]/) {
      $where = $1; # other placement can be given, e.g. @float[tbp]
    }
    $arg =~ m/(\@anchor.+)/;
    my $label = transform($1, 'figure');
    $arg =~ m/(\@ifinfo.*?\@end\s+ifinfo)/ms; 
    my $asciiart = transform($1);
    if (substr($arg, $+[0]) =~ m/(\@example.*?\@end\s+example)/ms) {
      $asciiart .= "\n" . transform($1);
    }
    my $image = '';
    if ($arg =~ m/(\@image.+)/) {
      $image = transform($1);
    }
    substr($arg, $+[0]) =~ m/(\@caption.+)/;
    my $caption = transform($1);
    # Handle short captions differently:
    if (length($caption) < 69 or substr($caption, -6) eq '@short') { 
      $caption =~ s/\@short$//;
      $caption = "\\par\\bigskip\n\\noindent\n" . $caption;
    } else {
      $caption = "\\begin\{quote\}\n" . $caption . "\n\\end\{quote\}";
    }
    return  "\\begin\{figure\}\[$where\]\n$label\n\\centering\n" . 
            "$asciiart\n$image\n$caption\n\\end\{figure\}";
  }
}

sub image { # 
  return sub {
    my $arg = shift;
    my ($file, $width, $height, $alt, $ext) = split(/\s*,\s*/, $arg);
    my $filename = $file . $ext;
    my $dimension = '';
    if ($width) {
      $dimension = "width=$width";
    } elsif ($height) {
      $dimension = "height=$height";
    }
    return "\\includegraphics\[$dimension\]\{$filename\}";
  }
}

# Texinfo -> LaTeX mapping
# =========================
my %syntax = (

# Type 1: non-alphabetic tags, like @*
# -------------------------------------
   '@-'	            => [ $void,	    bounce('') ],  # \\-
   '@/'	            => [ $void,	    bounce('') ],
   '@`'	            => [ $void,	    bounce("\\`") ],
   '@^'	            => [ $void,	    bounce('\\^') ],
   '@"'	            => [ $void,	    bounce('\\"') ],
   '@{'	            => [ $void,	    bounce('{') ],
   '@}'	            => [ $void,	    bounce('}') ],
   '@@'	            => [ $void,	    bounce('@') ],
   '@*'	            => [ $void,	    bounce('\\\\') ],
   '@\''	    => [ $void,	    bounce("\\'") ],
   '@|'	            => [ $void,	    bounce('') ],
   '@,'	            => [ $void,	    bounce('\\c') ],

# Type 2: alphabetic tags without arguments, like @dots{}
# --------------------------------------------------------
  '@copyright'      => [ $braces,   bounce('{\\copyright}') ],
  '@dots'           => [ $braces,   bounce('\\( \\dots \\)') ],
  '@TeX'            => [ $braces,   bounce('{\\TeX}') ],
  '@XeTeX'          => [ $braces,   bounce('{\\XeTeX}') ],
  '@LaTeX'          => [ $braces,   bounce('{\\LaTeX}') ],
  '@XeLaTeX'        => [ $braces,   bounce('{\\XeLaTeX}') ],

# Type 3: tags that require arguments, like @acronym{GCD}
# --------------------------------------------------------
  '@acronym'        => [ $braces,   glue('acronym') ],
  '@anchor'         => [ $braces,   glue('label') ],
  '@b'              => [ $braces,   glue('textbf') ],
  '@caption'        => [ $braces,   caption() ],
  '@cite'           => [ $braces,   glue('textit') ],
  '@code'           => [ $braces,   glue('code') ],
  '@dfn'            => [ $void,     bounce('% ') ],
  '@emph'           => [ $braces,   glue('emph') ],
  '@file'           => [ $braces,   glue('texttt') ],
  '@footnote'       => [ $braces,   glue('footnote') ],
  '@i'              => [ $braces,   glue('textit') ],
  '@image'          => [ $braces,   image() ],
  '@math'           => [ $braces,   inlinemath() ],
  '@newterm'        => [ $braces,   glue('newterm') ],
  '@r'              => [ $braces,   glue('textrm') ],
  '@ref'            => [ $braces,   glue('link') ],
  '@strong'         => [ $braces,   glue('heading') ],
  '@t'              => [ $braces,   glue('texttt') ],
  '@titlefont'      => [ $void,     bounce('% ') ],
  '@url'            => [ $braces,   url() ],
  '@value'          => [ $braces,   value() ],
  '@var'            => [ $braces,   glue('var') ],
  '@w'              => [ $braces,   glue('mbox') ],

# Type 4: tags that take an entire line, like @chapter
# -----------------------------------------------------
  '@author'         => [ $void,     bounce('%') ],
  '@bullet'         => [ $void,     bounce('\\bullet') ],
  '@bye'            => [ $empty,    bounce('') ],
  '@center'         => [ $space,    bounce('') ],
  '@chapter'        => [ $line,     glue('chapter') ],
  '@cindex'         => [ $space,    bounce('% ') ],
  '@comment'        => [ $void,     bounce('%') ],
  '@c'              => [ $void,     bounce('%') ],
  '@dircategory'    => [ $void,     bounce('%') ],
  '@endpage'        => [ $empty,    bounce('') ],
  '@everyheading'   => [ $line,     bounce('') ],
  '@finalout'       => [ $empty,    bounce('') ],
  '@headings'       => [ $line,     bounce('%') ],
  '@heading'        => [ $void,     bounce('%') ],
  '@include'        => [ $line,     bounce('') ],
  '@input'          => [ $line,     bounce('') ],
  '@item'           => [ $void,     bounce('\\item') ],
  '@node'           => [ $line,     node() ],
  '@noindent'       => [ $void,     bounce('\\noindent') ],
  '@page'           => [ $empty,    bounce('') ],
  '@pocket'         => [ $empty,    bounce('') ],
  '@printindex'     => [ $line,	    bounce('\\printindex') ],
  '@section'        => [ $line,     glue('section') ],
  '@setfilename'    => [ $void,     bounce('%') ],
  '@setshortcontentsaftertitlepage' => [ $empty, bounce('') ],
  '@settitle'       => [ $void,     bounce('%') ],
  '@set'            => [ $line,     setvalue() ],
  '@sp'             => [ $line,     glue('vspace', 'em') ],
  '@subsection'     => [ $line,     glue('subsection') ],
  '@subsubheading'  => [ $line,     glue('subsubsection*') ],
  '@subsubsection'  => [ $line,     glue('subsubsection') ],
  '@subtitle'       => [ $void,     bounce('%') ],
  '@title'          => [ $void,     bounce('%') ],
  '@unnumbered'     => [ $line,     unnumbered('chapter*') ],
  '@vskip'          => [ $void,	    bounce('%') ],

# Type 5: tags that create an environment (e.g. @tex .. @end tex)
# ----------------------------------------------------------------
  '@direntry'       => [ $end->('direntry'),      enclose('comment') ],
  '@enumerate'      => [ $end->('enumerate'),     enumerate() ],
  '@example'        => [ $end->('example'),       enclose('example') ],
  '@float'          => [ $end->('float'),         figure() ],
  '@ifinfo'         => [ $end->('ifinfo'),        enclose('comment') ],
  '@itemize'        => [ $end->('itemize'),       itemize() ],
  '@lisp'           => [ $end->('lisp'),          enclose('scheme') ],
  '@macro'          => [ $end->('macro'),         enclose('comment') ],
  '@menu'           => [ $end->('menu'),          bounce('') ],
  '@quotation'      => [ $end->('quotation'),     enclose('quote') ],
  '@smallexample'   => [ $end->('smallexample'),  enclose('smallexample') ],
  '@smalllisp'      => [ $end->('smalllisp'),     enclose('smallscheme') ],
  '@tex'            => [ $end->('tex'),           displaymath() ],
  '@titlepage'      => [ $end->('titlepage'),     enclose('comment') ],

# Other tags
# -----------
   '%'              => [ $void,	    bounce('\\%') ],
   '$'              => [ $void,	    bounce('\\$') ],

);  

# Transformer that converts the given string 
# from Texinfo to LaTeX
# ===========================================

# It functions as a filter, passing through all
# the text it doesn't recongnize as a Texinfo tag.
# When it finds a tag given in 'Texinfo -> LaTeX mapping',
# it becomes alert and looks for an argument after the tag. 
# The argument syntax depends on the tag type and is described
# in the '%syntax' hashmap as the first element of the array.
# The second element of the array gives a function that creates 
# a corresponding LaTeX command using the extracted argument. 
# The result is appended to the filtered stream.

sub transform { # expects a string and an environment
  my $in = shift;  
  my $env = (shift or '');
  my ($out, $tag, $arg, $pointer) = ('', '', '', 0);
  my $toggle = '';
  if ($env eq 'code') { 
    $in =~ s/(?<=\S)-(?=\S)/\\-\//g;  # assist line break after dash
  }
  elsif ($env =~ m/scheme/) { $toggle = $textrigger; }
  while (substr($in, $pointer) =~ $texi_tag) {
    $tag = $+{tag}; 
    $out .= substr($in, $pointer, $-[0]);
    $pointer += $+[0];
    if (defined($syntax{$tag}) and 
        substr($in, $pointer) =~ $syntax{$tag}[0]) {
      $arg = scalar($+{arg});
      $pointer += $+[0];
      $out .= $toggle . $syntax{$tag}[1]->($arg, $env) . $toggle;
    } else {
      $out .= $tag;
    }
  }
  return $out . substr($in, $pointer);
}

# Input/Output
# =============

# Return contents of file as string
sub swallow {
  my $filename = shift;
  local $/;
  open my $fh, "<", $filename;
  return <$fh>;
}

# Write contents of string to file
sub pour {
  my ($string, $filename) = @_;
  open my $fh, ">", $filename;
  print $fh $string;
  close $fh;
}

# Get optional output filename
our($opt_o);
getopt('o');

my ($texifile, $texistring);

# Attempt to open Texinfo file
if ($texifile = $ARGV[0]) {
  $texistring = swallow($texifile);
} else {
  say "No input filename given.";
  say "Usage: texi-to-latex [-o <output>] <input>.";
  exit;
}

# Make the conversion
# ====================
say "Processing... (may take several minutes)";
my $latex_out = transform($texistring, '');
say "Done.";

# Write the converted file out
# =============================
my $outfile = $texifile;

if ($opt_o) { # output filename given using '-o' switch
  $outfile = $opt_o;
} elsif ($texifile =~ m/.texi$/) {  # we have a file with extension '.texi'
  $outfile =~ s/.texi$/.tex/;  # replace '.texi' with '.tex'
} else {
  $outfile =~ s/$/.tex/;       # otherwise just append '.tex'
}

$latex_out = $preamble . $latex_out . $postamble;
pour($latex_out, $outfile);

