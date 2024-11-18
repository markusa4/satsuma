// Copyright 2024 Markus Anders
// This file is part of satsuma 1.1.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PARSER_H
#define SATSUMA_PARSER_H
#include "cnf.h"
#include "cnf2wl.h"
#include <string>
#include <charconv>

void parse_dimacs_to_cnf2wl(std::string& filename, cnf2wl& formula, bool entered_file) {
    FILE* file = nullptr;
    if(entered_file) file = fopen(filename.c_str(), "r");
    else file = stdin;
    if(!file) terminate_with_error("could not open file '" + filename + "'");

    constexpr int line_buf_sz = 1024*8;
    char line_buffer[line_buf_sz];
    setvbuf(file, line_buffer, _IOFBF, line_buf_sz);
    flockfile(file);

    bool reserved = false;
    const char* last_conversion = nullptr;

    int nv = 0;
    int nc = 0;

    int line_num = 0;

    char m;
    char*  buffer_pt;
    int    literal;
    char   buffer[24];
    std::vector<int> construct_clause;

    while ((m = getc_unlocked(file)) != EOF) {
        [[likely]]
        ++line_num;
        //const char m = line[0];
        switch (m) {
            // a clause
            [[likely]]
            case '-':
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
            {
                // not possible to continue without allocating the memory first
                if (!reserved) terminate_with_error("formula must begin with 'p' line");
                construct_clause.clear();

                // we've already read the first digit of the first literal
                buffer_pt = buffer+1;
                buffer[0] = m;
                for(;;) {
                    [[likely]]

                    // read next literal digit-by-digit
                    while ((m = getc_unlocked(file)) >= '-') [[likely]] *(buffer_pt++) = m;

                    // allow to eat additional whitespace
                    //if(buffer_pos == 0 && (m == ' ' || m == '\t')) continue;

                    // the pointer arithmetic to get this going is evil, but this function is amazingly fast
                    literal = 0;
                    last_conversion = std::from_chars(buffer, buffer_pt, literal).ptr;
                    if (literal == 0) break; // either the clause ended, or an error in the conversion occurred
                    construct_clause.push_back(literal); // add literal to clause we're constructing
                    buffer_pt = buffer;
                }

                // check if error in conversion occurred
                if(last_conversion == buffer)
                    terminate_with_error("invalid conversion occured in line " +
                                          std::to_string(line_num) + ": '" + buffer +"'");

                // add the clause we've constructed
                formula.add_clause(construct_clause);
                break;
            }

            // the problem definition
            [[unlikely]]
            case 'p': {
                // eat 5 characters
                m = getc_unlocked(file); // == ' ' // should not be unsafe since getc will keep returning EOF once
                bool valid = (m == ' ' || m == '\t'); // reached
                m = getc_unlocked(file); // == 'c'
                valid = valid && (m == 'c' || m == 'C');
                m = getc_unlocked(file); // == 'n'
                valid = valid && (m == 'n' || m == 'N');
                m = getc_unlocked(file); // == 'f'
                valid = valid && (m == 'f' || m == 'F');
                m = getc_unlocked(file);
                valid = valid && (m == ' ' || m == '\t');

                // could not match up "p cnf "
                if (!valid) terminate_with_error("invalid problem definition not matching 'p cnf '");

                buffer_pt = buffer;
                while ((m = getc_unlocked(file)) >= '-') *(buffer_pt++) = m;
                last_conversion = std::from_chars(buffer, buffer_pt, nv).ptr;
                if(last_conversion == buffer)
                    terminate_with_error("could not parse integer in line " + std::to_string(line_num)
                                                                   + ": '" + std::string(buffer) + "'");

                buffer_pt = buffer;
                while ((m = getc_unlocked(file)) >= '-') *(buffer_pt++) = m;
                last_conversion = std::from_chars(buffer, buffer_pt, nc).ptr;
                if(last_conversion == buffer)
                    terminate_with_error("could not parse integer in line " + std::to_string(line_num)
                                         + ": '" + std::string(buffer) + "'");

                reserved = true;
                formula.reserve(nv, nc);
                break;
            }

            [[unlikely]]
            case 'c': {
                while ((m = getc_unlocked(file)) != '\n' && m != '\r' && m != EOF);
                break;
            }

                // just eat whitespaces, carriage returns, and newlines
            [[unlikely]]
            case '\t':
            case ' ':
            case '\r':
            case '\n':
                break;

                // can not recognize, let's abort
            [[unlikely]]
            default: {
                terminate_with_error("can not parse line " + std::to_string(line_num));
                break;
            }
        }
    }

    funlockfile(file);
    if(!reserved) terminate_with_error("file did not contain an instance");
    std::clog << "\nc\t read " << (entered_file?ftell(file)/1000000.0:0.0) << "MB ";
    fclose(file);
}

#endif //SATSUMA_PARSER_H
