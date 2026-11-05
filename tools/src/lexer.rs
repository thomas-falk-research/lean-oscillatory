//! Lexical view of Lean source: comments and string/char literals blanked out (newlines kept, so line numbers
//! survive), then identifier-boundary token search. A tripwire, not a parser: the kernel replay is the check.

pub fn strip(src: &str) -> String {
    let c: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let blank = |ch: char| if ch == '\n' { '\n' } else { ' ' };
    while i < c.len() {
        if c[i] == '-' && c.get(i + 1) == Some(&'-') {
            while i < c.len() && c[i] != '\n' {
                out.push(' ');
                i += 1;
            }
        } else if c[i] == '/' && c.get(i + 1) == Some(&'-') {
            let mut depth = 0usize;
            while i < c.len() {
                if c[i] == '/' && c.get(i + 1) == Some(&'-') {
                    depth += 1;
                    out.push_str("  ");
                    i += 2;
                } else if c[i] == '-' && c.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    out.push_str("  ");
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    out.push(blank(c[i]));
                    i += 1;
                }
            }
        } else if c[i] == '"' {
            out.push(' ');
            i += 1;
            while i < c.len() && c[i] != '"' {
                if c[i] == '\\' && i + 1 < c.len() {
                    out.push(' ');
                    i += 1;
                }
                out.push(blank(c[i]));
                i += 1;
            }
            out.push(' ');
            i += 1;
        } else if c[i] == '\'' && i + 2 < c.len() && (c[i + 2] == '\'' || (c[i + 1] == '\\' && i + 3 < c.len() && c[i + 3] == '\''))
            && (i == 0 || !is_ident(c[i - 1]))
        {
            let len = if c[i + 1] == '\\' { 4 } else { 3 };
            for _ in 0..len {
                out.push(' ');
            }
            i += len;
        } else {
            out.push(c[i]);
            i += 1;
        }
    }
    out
}

pub fn is_ident(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '!' | '?' | '.') || ('\u{2080}'..='\u{209c}').contains(&ch)
}

/// Positions (1-based line numbers) of `word` occurring with identifier boundaries on both sides.
pub fn find_word(stripped: &str, word: &str) -> Vec<usize> {
    let mut hits = Vec::new();
    for (ln, line) in stripped.lines().enumerate() {
        let chars: Vec<char> = line.chars().collect();
        let w: Vec<char> = word.chars().collect();
        let mut i = 0;
        while i + w.len() <= chars.len() {
            if chars[i..i + w.len()] == w[..]
                && (i == 0 || !is_ident(chars[i - 1]))
                && (i + w.len() == chars.len() || !is_ident(chars[i + w.len()]))
            {
                hits.push(ln + 1);
            }
            i += 1;
        }
    }
    hits
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn comments_and_strings_are_blanked() {
        let s = strip("a -- sorry\n/- sorry /- nested -/ sorry -/ b \"sorry\" 'x' sorry");
        assert_eq!(find_word(&s, "sorry"), vec![2]);
        assert_eq!(s.lines().count(), 2);
    }
    #[test]
    fn boundaries() {
        let s = strip("sorryAx foo.sorry axioms axiom");
        assert!(find_word(&s, "sorry").is_empty());
        assert_eq!(find_word(&s, "axiom"), vec![1]);
    }
}
