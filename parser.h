#ifndef SATSUMA_PARSER_H
#define SATSUMA_PARSER_H
#include "cnf.h"
#include <string>

void parse_dimacs_to_cnf(std::string& filename, cnf& formula, bool entered_file) {
    //std::istream& input; // = std::cin;
    std::ifstream infile_stream;
    if(entered_file) infile_stream.open(filename);
    std::istream& input = entered_file? infile_stream : std::cin;

    std::vector<std::vector<int>> incidence_list;
    std::string line;
    std::string nv_str, nc_str;
    std::string nv1_string;

    std::vector<int> construct_clause;
    size_t i;
    int nv = 0;
    int nc = 0;
    while (std::getline(input, line)) {
        char m = line[0];
        switch (m) {
            case 'p':
                for(i = 6; i < line.size() && line[i] != ' '; ++i) {
                    nv_str += line[i];
                }

                ++i;
                for(; i < line.size() && line[i] != ' '; ++i) {
                    nc_str += line[i];
                }
                nv = std::stoi(nv_str);
                nc = std::stoi(nc_str);

                formula.reserve(nv, nc);
                break;
            case '-':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
            case '0':
                i = 0;
                construct_clause.clear();

                while(i < line.size()) {
                    nv1_string = "";
                    for (; i < line.size() && line[i] != ' '; ++i) {
                        nv1_string += line[i];
                    }

                    int literal = std::stoi(nv1_string);
                    if(literal == 0) break;
                    construct_clause.push_back(literal);
                    ++i;
                }

                formula.add_clause(construct_clause);
                break;
            default:
                break;
        }
    }
}

#endif //SATSUMA_PARSER_H
